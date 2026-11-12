module

public import Green64.Library.Correlation.Part019
public import Green64.Library.Correlation.Part010
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Correlation / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryIndAnchoredCoordinates -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 700000

/-- Every prescribed active BIG mark is a zero of the single translated anchor. -/
def memoryIndFrozenAnchorAllowed {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod) : Prop :=
  ∀ (t : Fin (N+1)) (g : BG) (j : Fin (J+ell)),
    c g ((ω.2.1 t g).val j) +
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t.val :
        ZMod (bigMod g ((ω.2.1 t g).val j))) = 0

/-- Reconstruct actual source independent states from frozen coordinates and one
compatible BIG anchor. Every ordered mark remains a genuine zero-coordinate mark. -/
def memoryIndAnchoredStates {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c) :
    Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell :=
  fun t => (ω.1 t, memoryIndependentBIGStateFrom BP bigMod (J+ell)
    (memoryIndBIGTorusTranslate BP bigMod
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t.val) c)
    (fun g => ⟨(ω.2.1 t g).val, (ω.2.1 t g).property, ha t g⟩))

/-- Freezing the reconstructed states returns the entire original omega verbatim. -/
theorem memory_ind_anchored_states_frozen {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c) :
    memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
      (memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns ω k c ha) ω.2.2 = ω := by
  rfl

/-- Reconstructed states satisfy each actual BIG transport predicate, including
when the original Fourier, SMALL, or auxiliary coefficient is zero. -/
theorem memory_ind_anchored_states_transport {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c)
    (i : Fin N) :
    memoryIndOriginalBIGRowTransport SP smallMod BP bigMod J ell m patterns
      (memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns ω k c ha) ω.2.2 k i := by
  unfold memoryIndOriginalBIGRowTransport
  rw [memory_ind_original_D_eq_frozen_D, memory_ind_anchored_states_frozen]
  intro g
  funext p
  have hs := memory_frozen_source_offset_step SP smallMod BP bigMod
    J ell m patterns ω k i.val i.isLt
  have he : (⟨i.val,i.isLt⟩ : Fin N) = i := Fin.eta i i.isLt
  simp only [he] at hs
  change c g p + (memoryFrozenSourceOffset SP smallMod BP bigMod
    J ell m patterns ω k (i.val+1) : ZMod (bigMod g p)) =
    (c g p + (memoryFrozenSourceOffset SP smallMod BP bigMod
      J ell m patterns ω k i.val : ZMod (bigMod g p))) +
    ((physicalAlternatingSign i.val*k*
      (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ) : ℤ) :
        ZMod (bigMod g p))
  have ho : memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k (i.val+1) =
      memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k i.val +
        physicalAlternatingSign i.val*k*
          (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ) := by omega
  rw [ho, Int.cast_add, add_assoc]

/-- The reconstructed initial full BIG torus is exactly the specified anchor. -/
theorem memory_ind_anchored_states_initial {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c) :
    (fun g => Green64SmallHaar.residues (bigMod g) (J+ell)
      ((memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns ω k c ha 0).2 g)) = c := by
  funext g p
  change c g p + (memoryFrozenSourceOffset SP smallMod BP bigMod
    J ell m patterns ω k 0 : ZMod (bigMod g p)) = c g p
  rw [memory_frozen_source_offset_zero]
  simp only [Int.cast_zero, add_zero]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndAnchoredDamping -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
set_option maxHeartbeats 700000

theorem memory_ind_frozen_visit_mem_iff {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (gp : PhysicalSourcePrime BP) (t : Fin (N+1)) :
    t.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp ↔
      ∃ j, (ω.2.1 t gp.1).val j = gp.2 := by
  simp only [memoryFrozenSourceVisits, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s,hs,hst⟩
    have he : s = t := Fin.ext hst
    simpa only [he] using hs
  · intro h
    exact ⟨t,h,rfl⟩

/-- Actual anchored visit damping is the entire original BIG Haar numerator
integrand, including active-hit constraints and all inactive primes. -/
theorem memory_ind_anchored_visit_damping {N : ℕ}
    (q : ℝ) (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c) :
    memoryIndOriginalVisitDamping SP smallMod BP bigMod J ell q
      (memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns ω k c ha) =
    (memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q N)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω) (N+1) c : ℂ) := by
  let states := memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns ω k c ha
  let A := memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
  let off := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  have hr : (∏ t : Fin (N+1), ∏ g : BG, sourceVisitQ q N t.val ^
      (Green64SmallHaar.omega (bigMod g)
        (Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g))-(J+ell))) =
      memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q N) off A (N+1) c := by
    unfold memoryIndBIGPhysicalAnchorIntegrand
    rw [Finset.prod_comm]
    conv_rhs => rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro g hg
    let act (t : Fin (N+1)) : Finset (BP g) :=
      (Finset.univ : Finset (Fin (J+ell))).image ((ω.2.1 t g).val)
    let C (t : Fin (N+1)) := Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g)
    have hl (t : Fin (N+1)) : sourceVisitQ q N t.val ^
        (Green64SmallHaar.omega (bigMod g) (C t)-(J+ell)) =
        ∏ p : BP g, if p ∈ act t then (1:ℝ)
          else if C t p = 0 then sourceVisitQ q N t.val else 1 := by
      have hs : act t ⊆ Green64SmallHaar.zeroCoordSet (bigMod g) (C t) := by
        intro p hp
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← he]
        exact Green64SmallHaar.marked_zero (bigMod g) (J+ell) ((states t).2 g) j
      have hc : (act t).card = J+ell := by
        unfold act
        rw [Finset.card_image_of_injective _ (ω.2.1 t g).property]
        simp
      simpa only [Green64SmallHaar.omega,Green64SmallHaar.zeroCoordSet,
        Finset.mem_filter,Finset.mem_univ,true_and] using
        (memory_generic_marked_zero_power_product
          (Green64SmallHaar.zeroCoordSet (bigMod g) (C t))
          (act t) hs (J+ell) hc (sourceVisitQ q N t.val))
    calc
      _ = ∏ t : Fin (N+1), ∏ p : BP g, if p ∈ act t then (1:ℝ)
          else if C t p = 0 then sourceVisitQ q N t.val else 1 := by
        apply Finset.prod_congr rfl
        intro t ht
        exact hl t
      _ = ∏ p : BP g, ∏ t : Fin (N+1), if p ∈ act t then (1:ℝ)
          else if C t p = 0 then sourceVisitQ q N t.val else 1 := Finset.prod_comm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        have hact : ∀ i ∈ A ⟨g,p⟩, c g p + (off i : ZMod (bigMod g p)) = 0 := by
          intro i hi
          obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨j,hj⟩ := (Finset.mem_filter.mp ht).2
          change (ω.2.1 t g).val j = p at hj
          subst p
          exact ha t g j
        rw [if_pos hact]
        rw [← Fin.prod_univ_eq_prod_range]
        apply Finset.prod_congr rfl
        intro t ht
        have hm : t.val ∈ A ⟨g,p⟩ ↔ p ∈ act t := by
          rw [memory_ind_frozen_visit_mem_iff SP smallMod BP J ell m patterns]
          simp only [act, Finset.mem_image, Finset.mem_univ, true_and]
        have hh : C t p = c g p + (off t.val : ZMod (bigMod g p)) := rfl
        by_cases hm' : p ∈ act t
        · rw [if_pos hm', if_pos (hm.mpr hm')]
        · rw [if_neg hm', if_neg (fun h => hm' (hm.mp h)), hh]
          by_cases hz : c g p + (off t.val : ZMod (bigMod g p)) = 0
          · rw [if_pos hz,if_pos hz]
            change sourceVisitQ q N t.val = 1-(1-sourceVisitQ q N t.val)*1
            ring
          · rw [if_neg hz,if_neg hz,mul_zero,sub_zero]
  have hc := congrArg Complex.ofReal hr
  simpa only [memoryIndOriginalVisitDamping, Complex.ofReal_prod] using hc
end Green64FullPhysicalE

end

end

/-! ## AllPrimeCoordinates -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Full original marks and frames after removing BOTH residue tori.
The two ordered injective mark families and all Nu/aux/four-permutation
frames remain. No residues or endpoint coefficients enter this carrier. -/
abbrev B643AllPrimePath434 (N : ℕ) :=
  (Fin (N+1) → (g : SG) → {f : Fin (J+ell) → SP g // Function.Injective f}) ×
  (Fin (N+1) → (g : BG) → {f : Fin (J+ell) → BP g // Function.Injective f}) ×
  (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)

noncomputable instance (N : ℕ) : Fintype
    (B643AllPrimePath434 SP BP J ell m patterns N) := by
  classical
  letI : Fintype ((g : SG) → {f : Fin (J+ell) → SP g // Function.Injective f}) := inferInstance
  letI : Fintype ((g : BG) → {f : Fin (J+ell) → BP g // Function.Injective f}) := inferInstance
  letI : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := inferInstance
  unfold B643AllPrimePath434
  infer_instance

/-- Verbatim mark/frame readout of an original independent source array. -/
def b643AllPrimePathOf434 {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) :
    B643AllPrimePath434 SP BP J ell m patterns N :=
  (fun t g => ⟨Green64SmallHaar.marks (smallMod g) (J+ell) ((states t).1 g),
    Green64SmallHaar.marks_injective (smallMod g) (J+ell) ((states t).1 g)⟩,
   fun t g => ⟨Green64SmallHaar.marks (bigMod g) (J+ell) ((states t).2 g),
    Green64SmallHaar.marks_injective (bigMod g) (J+ell) ((states t).2 g)⟩,
   frames)

/-- The unchanged original divisor: shared SMALL/BIG marks and repeated
auxiliary prime draws are all retained with their original multiplicity. -/
def b643AllPrimeD434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (i : Fin N) : ℕ :=
  let f := ω.2.2 i
  (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
    smallMod g ((ω.1 i.castSucc g).val (f.2.2.2.1 g j))) *
  (∏ g : BG,
    (∏ j ∈ sourceBigShared J ell m (patterns f.1.1) g,
      bigMod g ((ω.2.1 i.castSucc g).val (f.2.1 g j))) *
    (∏ j : ↥((patterns f.1.1).free g), bigMod g (f.1.2 g j)))

/-- The actual signed integer path, with fixed zero starting displacement. -/
def b643AllPrimeOffset434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) (t : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val < t then physicalAlternatingSign i.val*k*
    (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) else 0

/-- Both deterministic residue transports in the ORIGINAL row. -/
def b643AllPrimeRowTransport434 {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (k : ℤ) (i : Fin N) : Prop :=
  let delta : ℤ := physicalAlternatingSign i.val*k*
    (memoryIndependentD SP smallMod BP bigMod J ell m (patterns (frames i).1.1)
      (frames i).1.2 (states i.castSucc) (frames i).2.1 (frames i).2.2.2.1 : ℤ)
  (∀ g, Green64SmallHaar.residues (smallMod g) (J+ell) ((states i.succ).1 g) =
    Green64SmallHaar.translate (smallMod g) delta
      (Green64SmallHaar.residues (smallMod g) (J+ell) ((states i.castSucc).1 g))) ∧
  (∀ g, Green64SmallHaar.residues (bigMod g) (J+ell) ((states i.succ).2 g) =
    Green64SmallHaar.translate (bigMod g) delta
      (Green64SmallHaar.residues (bigMod g) (J+ell) ((states i.castSucc).2 g)))

/-- The coefficient retains precisely the original non-residue guards:
orientation, nonzero shift, auxiliary endpoint bans, and all shared slots. -/
def b643AllPrimeEdgeAllowed434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) (i : Fin N) : Prop :=
  let f := ω.2.2 i
  (physicalAlternatingSign i.val=1 ∨ physicalAlternatingSign i.val = -1) ∧ k≠0 ∧
  (∀ (g : BG) (j : ↥((patterns f.1.1).free g)) (a : Fin (J+ell)),
    f.1.2 g j ≠ (ω.2.1 i.castSucc g).val a ∧ f.1.2 g j ≠ (ω.2.1 i.succ g).val a) ∧
  (∀ (g : BG) (j : Fin (J+ell)), j ∈ sourceBigShared J ell m (patterns f.1.1) g →
    (ω.2.1 i.castSucc g).val (f.2.1 g j) = (ω.2.1 i.succ g).val (f.2.2.1 g j)) ∧
  (∀ (g : SG) (j : Fin (J+ell)), j ∈ sourceSmallShared J ell g →
    (ω.1 i.castSucc g).val (f.2.2.2.1 g j) = (ω.1 i.succ g).val (f.2.2.2.2 g j))

/-- Complete original complex edge coefficient, now independent of BOTH
initial anchors. The global complex Knu/Fourier scalar is charged once. -/
def b643AllPrimeEdgeWeight434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (i : Fin N) : ℂ :=
  let f := ω.2.2 i
  let D := b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i
  let o := physicalAlternatingSign i.val
  if b643AllPrimeEdgeAllowed434 SP BP J ell m patterns ω k i then
    (sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    (∏ g : BG, 1 / (Vbig g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceBigShared J ell m (patterns f.1.1) g)) *
    (∏ g : SG, 1 / (Vsmall g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceSmallShared J ell g)) *
    originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
        (fun g j => (ω.2.1 i.castSucc g).val (f.2.1 g j))
        (fun g j => (ω.2.1 i.succ g).val (f.2.2.1 g j))) zeta theta D o k
  else 0

/-- Both initial V^-M mark masses and all original row coefficients.
Only the two genuine initial Haar torus masses are outside this weight. -/
def b643AllPrimeWeight434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) : ℂ :=
  (∏ g : SG, 1/(Vsmall g : ℂ)^(J+ell)) *
  (∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)) *
  ∏ i : Fin N, b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
    Vsmall Vbig Knu zeta theta k ω i

/-- Actual visits for an arbitrary original group family. Equal offsets
at different time indices are retained as different visits. -/
def b643MarkVisits434 {G : Type} [Fintype G] (P : G → Type) [∀ g, Fintype (P g)]
    [∀ g, DecidableEq (P g)] (M N : ℕ)
    (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (p : Sigma P) : Finset ℕ :=
  (Finset.univ : Finset (Fin (N+1))).filter
    (fun t => ∃ j, (marks t p.1).val j=p.2) |>.image Fin.val

theorem b643_all_prime_D_readout434 {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) (i : Fin N) :
    b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) i =
    memoryIndependentD SP smallMod BP bigMod J ell m (patterns (frames i).1.1)
      (frames i).1.2 (states i.castSucc) (frames i).2.1 (frames i).2.2.2.1 := rfl

/-- Source-exact same offset: no changed shift, prime power, frame or mark. -/
theorem b643_all_prime_offset_readout434 {N : ℕ}
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) (k : ℤ) :
    b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) k =
    memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames) k := rfl
end Green64FullPhysicalE

end

end

