module

public import Green64.Library.Correlation.PhysicalNoRepeatDensity
public import Green64.Library.Weights.ReachableBackgroundEncoding

@[expose] public section

/-!
# Correlation / PhysicalReturnCoordinates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalReturnCoordinates -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem mapped_sum_prod {I U : Type} [DecidableEq I]
    (S : Finset I) (m : I → Multiset U) (f : U → ℝ) :
    ((∑ i ∈ S,m i).map f).prod = ∏ i ∈ S,((m i).map f).prod := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi,Multiset.map_add,Multiset.prod_add,
        ih,Finset.prod_insert hi]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

theorem source_original_RETURN_pending_seen_injective434 (shift : ℤ) :
    Function.Injective (fun s : SourceOriginalPrimeReturnProductState434 modulus =>
      (sourceOriginalPrimeProductPending434 modulus shift s,
        sourceOriginalPrimeProductSeen434 modulus s)) := by
  intro s t h
  have hp := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp only at hp hs
  funext p
  have hpend := congrArg (fun m : Multiset (Atom P modulus) =>
    m.filter (fun z => z.1=p)) hp
  simp only [source_original_PRIME_PRODUCT_pending_filter434] at hpend
  have hseen : sourceOriginalOnePrimeSeen434 (s p)=true ↔
      sourceOriginalOnePrimeSeen434 (t p)=true := by
    rw [←source_original_PRIME_PRODUCT_seen_mem434,
      ←source_original_PRIME_PRODUCT_seen_mem434,hs]
  cases hsp : s p <;> cases htp : t p <;>
    simp_all [sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434]

/-- Product coordinate density equals the literal pending atom product.
The accumulated translation has no effect on this original measure. -/
theorem source_original_RETURN_density_pending_product434
    (shift : ℤ) (V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    ((sourceOriginalPrimeProductPending434 modulus shift s).map
      (fun z => V*mu z.1)).prod =
    sourceOriginalPrimeReturnDensity434 modulus V mu s := by
  rw [sourceOriginalPrimeProductPending434,mapped_sum_prod]
  apply Finset.prod_congr rfl
  intro p hp
  cases s p <;> simp [sourceOriginalOnePrimePending434,sourceOriginalReturnPendingMass434]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

abbrev SourceOriginalFullReturnState434 :=
  (g : BG) → SourceOriginalPrimeReturnProductState434 (bm g)

def sourceOriginalFullReturnSeen434
    (s : SourceOriginalFullReturnState434 BP bm) : Finset ℕ :=
  Finset.univ.biUnion (fun g => (sourceOriginalPrimeProductSeen434 (bm g) (s g)).image (bm g))

theorem source_original_FULL_RETURN_seen_mem434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (s : SourceOriginalFullReturnState434 BP bm) (g : BG) (p : BP g) :
    bm g p ∈ sourceOriginalFullReturnSeen434 BP bm s ↔
      p ∈ sourceOriginalPrimeProductSeen434 (bm g) (s g) := by
  constructor
  · intro h
    obtain ⟨h,hh,hmem⟩ := Finset.mem_biUnion.mp h
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hmem
    have heq : (⟨h,r⟩ : Sigma BP)=⟨g,p⟩ := hi he
    cases heq
    exact hr
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

variable (M : ℕ)

abbrev SourceOriginalFullReturnCoordinate434 :=
  GroupState SP sm M × ((g : BG) → Fin M → BP g) × SourceOriginalFullReturnState434 BP bm

def sourceOriginalFullReturnDecode434
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) :
    FullPhysicalOutput SP sm BP bm M × Finset ℕ :=
  ((x.1,fun g => (x.2.1 g,sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g))),
    sourceOriginalFullReturnSeen434 BP bm x.2.2)

def sourceOriginalFullReturnDensity434 (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) : ℝ :=
  groupStateMass SP sm M Vs *
    ∏ g,activeMass M (mu g) (x.2.1 g) *
      sourceOriginalPrimeReturnDensity434 (bm g) (Vb g) (mu g) (x.2.2 g)

/-- No label or history multiplicity: globally injective numerical prime
labels make the full SMALL/active/return decoding injective. -/
theorem source_original_FULL_RETURN_decode_injective434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2)) :
    Function.Injective (sourceOriginalFullReturnDecode434 SP sm BP bm M) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M × Finset ℕ => z.1.1) h
  · apply Prod.ext
    · funext g
      exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M × Finset ℕ => (z.1.2 g).1) h
    · funext g
      apply source_original_RETURN_pending_seen_injective434 (bm g) 0
      apply Prod.ext
      · exact congrArg (fun z : FullPhysicalOutput SP sm BP bm M × Finset ℕ => (z.1.2 g).2) h
      · ext p
        rw [←source_original_FULL_RETURN_seen_mem434 BP bm hi,
          ←source_original_FULL_RETURN_seen_mem434 BP bm hi]
        exact Iff.of_eq (congrArg (fun z : FullPhysicalOutput SP sm BP bm M × Finset ℕ =>
          bm g p ∈ z.2) h)

variable (J ell : ℕ) (cap : BG → ℕ)

/-- Every actual reachable Fock×seen state has these coordinates. This uses
the original global inventory and the actual numeric prime-pool support. -/
theorem source_original_ACTUAL_full_return_exists434
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap) :
    ∃ x : SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell),
      sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x=a.val := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  let seen := fun g => (Finset.univ : Finset (BP g)).filter (fun p => bm g p ∈ a.val.2)
  have hl (g : BG) :
      ((a.val.1.2 g).2.map (fun z => bm g z.1)) ≤
        sourceOriginalPhysicalInventory434 SP sm BP bm (J+ell) a.val.1 := by
    apply le_trans (b:=sourceOriginalBigInventory434 (bm g) (J+ell)
      (a.val.1.2 g).1 (a.val.1.2 g).2) le_add_self
    have hh := Finset.sum_le_sum_of_subset
      (f:=fun g => sourceOriginalBigInventory434 (bm g) (J+ell)
        (a.val.1.2 g).1 (a.val.1.2 g).2)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ g))
    simpa only [Finset.sum_singleton,sourceOriginalPhysicalInventory434] using hh
  have henc (g : BG) : ∃ s : SourceOriginalPrimeReturnProductState434 (bm g),
      sourceOriginalPrimeProductPending434 (bm g) 0 s=(a.val.1.2 g).2 ∧
      sourceOriginalPrimeProductSeen434 (bm g) s=seen g := by
    apply source_original_PHYSICAL_PENDING_return_encoding434
    · apply Multiset.Nodup.of_map (bm g)
      simpa only [Multiset.map_map,Function.comp_def] using
        (Multiset.nodup_of_le (hl g) ha.2.2.1)
    · intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,ha.2.2.2 _ ?_⟩
      exact Multiset.mem_of_le (hl g) (Multiset.mem_map.mpr ⟨z,hz,rfl⟩)
  choose s hp hs using henc
  refine ⟨(a.val.1.1,(fun g => (a.val.1.2 g).1),s),?_⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext g
      exact Prod.ext rfl (hp g)
  · change sourceOriginalFullReturnSeen434 BP bm s=a.val.2
    unfold sourceOriginalFullReturnSeen434
    simp_rw [hs]
    ext n
    constructor
    · intro hn
      obtain ⟨g,hg,hm⟩ := Finset.mem_biUnion.mp hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
      exact (Finset.mem_filter.mp hp).2
    · intro hn
      have hpool := Finset.mem_powerset.mp ha.2.1 hn
      obtain ⟨g,hg,hm⟩ := Finset.mem_biUnion.mp hpool
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩⟩

/-- This is the original physical density at every actual decoded state,
not a new product probability or a density chosen separately per visit. -/
theorem source_original_ACTUAL_full_return_density434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell))
    (hx : sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x=a.val) :
    sourceOriginalFullReturnDensity434 SP sm BP bm (J+ell) Vs Vb mu x =
      sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu a := by
  rw [source_original_ACTUAL_true_density_pending_product434]
  unfold sourceOriginalFullReturnDensity434
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  have ha := congrArg (fun z : FullPhysicalOutput SP sm BP bm (J+ell) × Finset ℕ =>
    (z.1.2 g).1) hx
  have hp := congrArg (fun z : FullPhysicalOutput SP sm BP bm (J+ell) × Finset ℕ =>
    (z.1.2 g).2) hx
  change x.2.1 g=(a.val.1.2 g).1 at ha
  change sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g)=(a.val.1.2 g).2 at hp
  rw [←ha,←hp,source_original_RETURN_density_pending_product434]

end Green64Analytic.CorrelationSquare

end

end

