module

public import Green64.Library.Analysis.Estimates.AllPrimeRow
public import Green64.Library.Correlation.Part020
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Correlation.Part019
public import Green64.Library.Correlation.MemorySourceRootLifespanReadout
public import Green64.Library.Correlation.Part018

@[expose] public section

/-!
# Correlation / Part021

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IntegerPhysicalState -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ)

/-- Every source residue coordinate is the SAME physical integer.
The state already contains the original ordered injective zero-mark lists. -/
def b650IntegerResidueAt434 (n : ℤ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) : Prop :=
  (∀ g p, Green64SmallHaar.residues (smallMod g) (J+ell) (x.1 g) p =
    (n:ZMod (smallMod g p))) ∧
  (∀ g p, Green64SmallHaar.residues (bigMod g) (J+ell) (x.2 g) p =
    (n:ZMod (bigMod g p)))

/-- Original physical marked states at one signed integer, expressed
literally by divisibility and ordered distinct labels in EACH group. -/
abbrev B650IntegerMarks434 (n : ℤ) :=
  ((g : SG) → {f : Fin (J+ell) → SP g // Function.Injective f ∧
    ∀ j, (smallMod g (f j):ℤ) ∣ n}) ×
  ((g : BG) → {f : Fin (J+ell) → BP g // Function.Injective f ∧
    ∀ j, (bigMod g (f j):ℤ) ∣ n})

/-- Source-exact physical carrier equivalence. No independent torus
coordinates remain, no norm is imposed on the mark fibre, and n=0
uses ordinary integer divisibility. -/
def b650IntegerStateMarksEquiv434 (n : ℤ) :
    {x : MemoryIndependentState SP smallMod BP bigMod J ell //
      b650IntegerResidueAt434 SP smallMod BP bigMod J ell n x} ≃
    B650IntegerMarks434 SP smallMod BP bigMod J ell n where
  toFun x :=
    ((fun g => ⟨Green64SmallHaar.marks (smallMod g) (J+ell) (x.val.1 g),
      Green64SmallHaar.marks_injective (smallMod g) (J+ell) (x.val.1 g), by
        intro j
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd n _).mp
        rw [← x.property.1 g (Green64SmallHaar.marks (smallMod g) (J+ell) (x.val.1 g) j)]
        exact Green64SmallHaar.marked_zero (smallMod g) (J+ell) (x.val.1 g) j⟩),
     (fun g => ⟨Green64SmallHaar.marks (bigMod g) (J+ell) (x.val.2 g),
      Green64SmallHaar.marks_injective (bigMod g) (J+ell) (x.val.2 g), by
        intro j
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd n _).mp
        rw [← x.property.2 g (Green64SmallHaar.marks (bigMod g) (J+ell) (x.val.2 g) j)]
        exact Green64SmallHaar.marked_zero (bigMod g) (J+ell) (x.val.2 g) j⟩))
  invFun marks := ⟨
    (memoryIndependentBIGStateFrom SP smallMod (J+ell)
      (fun g p => (n:ZMod (smallMod g p)))
      (fun g => ⟨(marks.1 g).val,(marks.1 g).property.1,
        fun j => (ZMod.intCast_zmod_eq_zero_iff_dvd n _).mpr ((marks.1 g).property.2 j)⟩),
     memoryIndependentBIGStateFrom BP bigMod (J+ell)
      (fun g p => (n:ZMod (bigMod g p)))
      (fun g => ⟨(marks.2 g).val,(marks.2 g).property.1,
        fun j => (ZMod.intCast_zmod_eq_zero_iff_dvd n _).mpr ((marks.2 g).property.2 j)⟩)),
    (fun _ _ => rfl),(fun _ _ => rfl)⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext g
      apply Subtype.ext
      apply Prod.ext
      · funext p
        exact (x.property.1 g p).symm
      · rfl
    · funext g
      apply Subtype.ext
      apply Prod.ext
      · funext p
        exact (x.property.2 g p).symm
      · rfl
  right_inv marks := by
    apply Prod.ext
    · funext g
      apply Subtype.ext
      rfl
    · funext g
      apply Subtype.ext
      rfl

/-- Finite physical states in an arbitrary finite signed position set.
The finite truncation retains ALL original marks at every position. -/
abbrev B650IntegerPhysicalState434 (positions : Finset ℤ) :=
  {v : positions × MemoryIndependentState SP smallMod BP bigMod J ell //
    b650IntegerResidueAt434 SP smallMod BP bigMod J ell v.1.val v.2}

noncomputable instance b650IntegerPhysicalFintype434 (positions : Finset ℤ) :
    Fintype (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) := by
  unfold B650IntegerPhysicalState434
  infer_instance

/-- An exact physical step implies BOTH native residue transports,
with the original signed displacement and no CRT hypothesis. -/
theorem b650_integer_residue_transport434 (positions : Finset ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (delta : ℤ) (hstep : y.val.1.val = x.val.1.val + delta) :
    (∀ g, Green64SmallHaar.residues (smallMod g) (J+ell) (y.val.2.1 g) =
      Green64SmallHaar.translate (smallMod g) delta
        (Green64SmallHaar.residues (smallMod g) (J+ell) (x.val.2.1 g))) ∧
    (∀ g, Green64SmallHaar.residues (bigMod g) (J+ell) (y.val.2.2 g) =
      Green64SmallHaar.translate (bigMod g) delta
        (Green64SmallHaar.residues (bigMod g) (J+ell) (x.val.2.2 g))) := by
  constructor
  · intro g
    funext p
    change Green64SmallHaar.residues (smallMod g) (J+ell) (y.val.2.1 g) p =
      Green64SmallHaar.residues (smallMod g) (J+ell) (x.val.2.1 g) p + (delta:ZMod (smallMod g p))
    rw [y.property.1 g p,x.property.1 g p,hstep,Int.cast_add]
  · intro g
    funext p
    change Green64SmallHaar.residues (bigMod g) (J+ell) (y.val.2.2 g) p =
      Green64SmallHaar.residues (bigMod g) (J+ell) (x.val.2.2 g) p + (delta:ZMod (bigMod g p))
    rw [y.property.2 g p,x.property.2 g p,hstep,Int.cast_add]

/-- Original physical mark mass, uniform over states but with no Haar
prime-denominator factor and no normalization of the mark fibres. -/
def b650IntegerStateMass434 (Vsmall : SG → ℝ) (Vbig : BG → ℝ) : ℝ :=
  (∏ g : SG, 1/(Vsmall g)^(J+ell)) * (∏ g : BG, 1/(Vbig g)^(J+ell))

theorem b650_integer_state_mass_positive434 (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (hVs : ∀ g, 0<Vsmall g) (hVb : ∀ g, 0<Vbig g) :
    0<b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig := by
  unfold b650IntegerStateMass434
  exact mul_pos (Finset.prod_pos (fun g _ => one_div_pos.mpr (pow_pos (hVs g) _)))
    (Finset.prod_pos (fun g _ => one_div_pos.mpr (pow_pos (hVb g) _)))
end Green64FullPhysicalE

end

end

/-! ## IntegerPhysicalFrame -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Reverse only the two endpoint permutations in BOTH prime families;
the actual pattern, auxiliary labels and their multiplicities stay fixed. -/
def b650SwapFrame434
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns :=
  (f.1,f.2.2.1,f.2.1,f.2.2.2.2,f.2.2.2.1)

theorem b650_swap_frame_involutive434
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650SwapFrame434 BP J ell m patterns (b650SwapFrame434 BP J ell m patterns f)=f := rfl

/-- The unchanged original numerical divisor, including every repeated
auxiliary draw, read from one complete source frame. -/
def b650NativeFrameD434
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℕ :=
  memoryIndependentD SP smallMod BP bigMod J ell m (patterns f.1.1)
    f.1.2 x f.2.1 f.2.2.2.1

/-- Literal shared-label equalities at the two permuted physical endpoints. -/
def b650NativeFrameShares434
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : Prop :=
  (∀ (g : SG) (j : Fin (J+ell)), j ∈ sourceSmallShared J ell g →
    Green64SmallHaar.marks (smallMod g) (J+ell) (x.1 g) (f.2.2.2.1 g j) =
    Green64SmallHaar.marks (smallMod g) (J+ell) (y.1 g) (f.2.2.2.2 g j)) ∧
  (∀ (g : BG) (j : Fin (J+ell)), j ∈ sourceBigShared J ell m (patterns f.1.1) g →
    Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (f.2.1 g j) =
    Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (f.2.2.1 g j))

theorem b650_frame_shared_reverse434
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650NativeFrameShares434 SP smallMod BP bigMod J ell m patterns y x
      (b650SwapFrame434 BP J ell m patterns f) ↔
    b650NativeFrameShares434 SP smallMod BP bigMod J ell m patterns x y f := by
  constructor
  · intro h
    exact ⟨fun g j hj => (h.1 g j hj).symm,fun g j hj => (h.2 g j hj).symm⟩
  · intro h
    exact ⟨fun g j hj => (h.1 g j hj).symm,fun g j hj => (h.2 g j hj).symm⟩

/-- Exact physical reversal preserves D. In particular no free-prime
multiplicity is erased and no estimate for the D20 mass is inferred. -/
theorem b650_frame_divisor_reverse434
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (hshare : b650NativeFrameShares434 SP smallMod BP bigMod J ell m patterns x y f) :
    b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns y
      (b650SwapFrame434 BP J ell m patterns f) =
    b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x f := by
  unfold b650NativeFrameD434 memoryIndependentD b650SwapFrame434
  dsimp only
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro j hj
    rw [hshare.1 g j hj]
  · apply Finset.prod_congr rfl
    intro g hg
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hshare.2 g j hj]

/-- All original real row factors, separate from the ONE global complex
Knu and its spectral phase. This contains actual V^-t target counting,
auxiliary harmonic law, all four permutation laws and BOTH dampings. -/
def b650NativeRealFrameWeight434
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℝ :=
  sourceAuxMass BP bigMod J m Vbig (patterns f.1.1) f.1.2 *
  bigEndpointPairMass (BG:=BG) (J+ell) *
  Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) *
  (∏ g : BG, 1/(Vbig g)^Green64SmallHaar.unsharedSlots (J+ell)
    (sourceBigShared J ell m (patterns f.1.1) g)) *
  (∏ g : SG, 1/(Vsmall g)^Green64SmallHaar.unsharedSlots (J+ell)
    (sourceSmallShared J ell g)) *
  (∏ g : SG, Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.1 g) *
    Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (y.1 g)) *
  (∏ g : BG, Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.2 g) *
    Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.2 g))

theorem b650_real_frame_weight_reverse434
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650NativeRealFrameWeight434 SP smallMod BP bigMod J ell m patterns q Vsmall Vbig y x
      (b650SwapFrame434 BP J ell m patterns f) =
    b650NativeRealFrameWeight434 SP smallMod BP bigMod J ell m patterns q Vsmall Vbig x y f := by
  unfold b650NativeRealFrameWeight434 b650SwapFrame434
  dsimp only
  have hs (g : SG) : Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (y.1 g) *
      Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.1 g) =
      Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.1 g) *
      Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (y.1 g) := mul_comm _ _
  have hb (g : BG) : Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.2 g) *
      Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.2 g) =
      Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.2 g) *
      Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (y.2 g) := mul_comm _ _
  simp_rw [hs,hb]

/-- Original physical frame guard: both endpoint lists are already
actual divisors of their integer; all shared and auxiliary bans stay. -/
def b650IntegerFrameAllowed434 (positions : Finset ℤ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : Prop :=
  (o=1 ∨ o = -1) ∧ k≠0 ∧
  memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns f.1.1) f.1.2 x.val.2 y.val.2 ∧
  b650NativeFrameShares434 SP smallMod BP bigMod J ell m patterns x.val.2 y.val.2 f ∧
  y.val.1.val = x.val.1.val+o*k*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 f:ℤ)

/-- Literal original finite physical row coefficient at one frame.
There is no independent residue averaging and no marked-list return. -/
def b650IntegerFrameScalar434 (positions : Finset ℤ)
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) : ℂ :=
  if b650IntegerFrameAllowed434 SP smallMod BP bigMod J ell m patterns positions o k x y f then
    (b650NativeRealFrameWeight434 SP smallMod BP bigMod J ell m patterns q Vsmall Vbig x.val.2 y.val.2 f : ℂ) *
    originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o f.1.1 f.1.2
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (x.val.2.2 g) (f.2.1 g j))
        (fun g j => Green64SmallHaar.marks (bigMod g) (J+ell) (y.val.2.2 g) (f.2.2.1 g j)))
      zeta 0 (b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 f) o k
  else 0
end Green64FullPhysicalE

end

end

/-! ## MemoryIndTransportFrozenEquiv -/

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

/-- Every transport-supported source array supplies a compatible full initial anchor. -/
theorem memory_ind_transport_anchor_allowed {N : ℕ}
    (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
      J ell m patterns states frames k i) :
    memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames) k
      (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g)) := by
  intro t g j
  have hc := memory_ind_transport_array_BIG_one_anchor SP smallMod BP bigMod
    J ell m patterns k states frames ht t
  have he := congrArg (fun C : MemoryIndependentBIGTorus BP bigMod =>
    C g (Green64SmallHaar.marks (bigMod g) (J+ell) ((states t).2 g) j)) hc
  exact he.symm.trans (Green64SmallHaar.marked_zero (bigMod g) (J+ell) ((states t).2 g) j)

/-- The complete supported state array is reconstructed, not merely its BIG marks. -/
theorem memory_ind_transport_reconstruct {N : ℕ}
    (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
      J ell m patterns states frames k i) :
    memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns
      (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames) k
      (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))
      (memory_ind_transport_anchor_allowed SP smallMod BP bigMod J ell m patterns
        k states frames ht) = states := by
  funext t
  apply Prod.ext
  · rfl
  · funext g
    apply Subtype.ext
    apply Prod.ext
    · exact (congrFun (memory_ind_transport_array_BIG_one_anchor SP smallMod BP bigMod
        J ell m patterns k states frames ht t) g).symm
    · rfl

/-- Exact supported-array bijection to frozen omega and one compatible BIG torus.
Zero Fourier/SMALL coefficients are not removed from either carrier. -/
def memoryIndTransportFrozenEquiv (N : ℕ) (k : ℤ) :
    {sf : ((Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
      (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)) //
      ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
        J ell m patterns sf.1 sf.2 k i} ≃
    {oc : (MemoryFrozenSourcePath SP smallMod BP J ell m patterns N ×
      MemoryIndependentBIGTorus BP bigMod) //
      memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns oc.1 k oc.2} where
  toFun sf := ⟨(memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns
      sf.val.1 sf.val.2,
    fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((sf.val.1 0).2 g)),
    memory_ind_transport_anchor_allowed SP smallMod BP bigMod J ell m patterns
      k sf.val.1 sf.val.2 sf.property⟩
  invFun oc := ⟨(memoryIndAnchoredStates SP smallMod BP bigMod J ell m patterns
      oc.val.1 k oc.val.2 oc.property, oc.val.1.2.2),
    memory_ind_anchored_states_transport SP smallMod BP bigMod J ell m patterns
      oc.val.1 k oc.val.2 oc.property⟩
  left_inv := by
    intro sf
    apply Subtype.ext
    apply Prod.ext
    · exact memory_ind_transport_reconstruct SP smallMod BP bigMod
        J ell m patterns k sf.val.1 sf.val.2 sf.property
    · rfl
  right_inv := by
    intro oc
    apply Subtype.ext
    apply Prod.ext
    · exact memory_ind_anchored_states_frozen SP smallMod BP bigMod
        J ell m patterns oc.val.1 k oc.val.2 oc.property
    · exact memory_ind_anchored_states_initial SP smallMod BP bigMod
        J ell m patterns oc.val.1 k oc.val.2 oc.property
end Green64FullPhysicalE

end

end

/-! ## MemoryIndAnchorIntegrandSupport -/

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

/-- Incompatible anchors have exactly zero ORIGINAL Haar numerator contribution. -/
theorem memory_ind_anchor_integrand_zero {N : ℕ}
    (q : ℝ) (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (k : ℤ) (c : MemoryIndependentBIGTorus BP bigMod)
    (ha : ¬ memoryIndFrozenAnchorAllowed SP smallMod BP bigMod J ell m patterns ω k c) :
    memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q N)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω) (N+1) c = 0 := by
  unfold memoryIndFrozenAnchorAllowed at ha
  obtain ⟨t,ht⟩ := not_forall.mp ha
  obtain ⟨g,hg⟩ := not_forall.mp ht
  obtain ⟨j,hj⟩ := not_forall.mp hg
  let gp : PhysicalSourcePrime BP := ⟨g,(ω.2.1 t g).val j⟩
  unfold memoryIndBIGPhysicalAnchorIntegrand
  apply Finset.prod_eq_zero (Finset.mem_univ gp)
  apply if_neg
  intro hall
  have hv : t.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp :=
    (memory_ind_frozen_visit_mem_iff SP smallMod BP J ell m patterns ω gp t).mpr ⟨j,rfl⟩
  exact hj (hall t.val hv)

/-- Full all-visit source damping on any transport-supported array, including
zero-weight paths, equals the unchanged physical one-anchor Haar integrand. -/
theorem memory_ind_transport_visit_damping {N : ℕ}
    (q : ℝ) (k : ℤ)
    (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
      J ell m patterns states frames k i) :
    memoryIndOriginalVisitDamping SP smallMod BP bigMod J ell q states =
    (memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q N)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns
        (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames) k)
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns
        (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames))
      (N+1) (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g)) : ℂ) := by
  have h := memory_ind_anchored_visit_damping SP smallMod BP bigMod J ell m patterns q
    (memoryIndOriginalFrozenPathOf SP smallMod BP bigMod J ell m patterns states frames) k
    (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))
    (memory_ind_transport_anchor_allowed SP smallMod BP bigMod J ell m patterns
      k states frames ht)
  rw [memory_ind_transport_reconstruct SP smallMod BP bigMod
    J ell m patterns k states frames ht] at h
  exact h
end Green64FullPhysicalE

end

end

/-! ## MemoryIndFullSumFrozenHaar -/

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

local instance : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := by
  classical
  unfold MemoryPrimitiveEFrame
  infer_instance
local instance (gp : PhysicalSourcePrime BP) :
    NeZero (physicalSourcePrimeValue BP bigMod gp) :=
  inferInstanceAs (NeZero (bigMod gp.1 gp.2))

/-- COMPLETE original weighted array sum equals the literal frozen source Haar sum.
The support bijection retains all zero terms and every original normalization. -/
theorem memory_ind_original_full_sum_frozen_Haar
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ) :
    (∑ states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell,
      ∑ frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns,
        memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k states frames) =
    ∑ ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (n+1),
      memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (memoryFrozenHaarExpectation (physicalSourcePrimeValue BP bigMod)
        (sourceVisitEta q (n+1))
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω) (n+2) : ℂ) := by
  classical
  let SF := (Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
    (Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
  let OC := MemoryFrozenSourcePath SP smallMod BP J ell m patterns (n+1) ×
    MemoryIndependentBIGTorus BP bigMod
  let P (sf : SF) := ∀ i, memoryIndOriginalBIGRowTransport SP smallMod BP bigMod
    J ell m patterns sf.1 sf.2 k i
  let Q (oc : OC) := memoryIndFrozenAnchorAllowed SP smallMod BP bigMod
    J ell m patterns oc.1 k oc.2
  let F (sf : SF) : ℂ := memoryIndOriginalArrayWeight SP smallMod BP bigMod
    J ell m patterns q Vsmall Vbig Knu zeta theta k sf.1 sf.2
  let G (oc : OC) : ℂ := (∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)) *
    (memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k oc.1 *
    (memoryIndBIGPhysicalAnchorIntegrand BP bigMod (sourceVisitEta q (n+1))
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns oc.1 k)
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns oc.1) (n+2) oc.2 : ℂ))
  have he : (∑ sf : SF, F sf) = ∑ oc : OC, G oc := by
    apply memory_generic_supported_sum_equiv P Q
      (memoryIndTransportFrozenEquiv SP smallMod BP bigMod J ell m patterns (n+1) k) F G
    · intro sf hf
      unfold F
      rw [memory_ind_original_full_array_weight_frozen SP smallMod BP bigMod
        J ell m patterns q hq Vsmall Vbig Knu zeta theta k n sf.1 sf.2,
        if_neg hf, mul_zero]
    · intro oc hg
      unfold G
      rw [memory_ind_anchor_integrand_zero SP smallMod BP bigMod
        J ell m patterns q oc.1 k oc.2 hg, Complex.ofReal_zero, mul_zero, mul_zero]
    · intro sf
      dsimp only [F,G,memoryIndTransportFrozenEquiv]
      rw [memory_ind_original_full_array_weight_frozen SP smallMod BP bigMod
        J ell m patterns q hq Vsmall Vbig Knu zeta theta k n sf.val.1 sf.val.2,
        if_pos sf.property]
      rw [memory_ind_transport_visit_damping SP smallMod BP bigMod J ell m patterns
        q k sf.val.1 sf.val.2 sf.property]
      rfl
  calc
    _ = ∑ sf : SF, F sf := by
      conv_rhs => rw [Fintype.sum_prod_type]
    _ = ∑ oc : OC, G oc := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ω hω
      dsimp only [G]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [memory_ind_BIG_Haar_mass_exact]
      rw [← memory_ind_BIG_physical_anchor_eq_original_frozen_Haar]
      unfold memoryIndBIGPhysicalHaarExpectation
      simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_prod,
        Complex.ofReal_natCast]
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl
end Green64FullPhysicalE

end

end

/-! ## MemorySourceCanonicalRootReadoutTarget -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig mu k N)

/-- Frozen actual active visits. No independent geometry is assumed. -/
def memorySourceWitnessActiveVisits (g : BG) (p : BP g) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun i => ∃ j, ((H.before i).2 g).1 j = p)

/-- UNPROVED READOUT STRUCTURE. Its fields are obligations to DERIVE from
an arbitrary nonzero source root, not permitted new theorem hypotheses.
The set-clock profile is proved; full residues, chronological seen equalities
and canonical representative fibres below remain to be proved together. -/
structure MemorySourceCanonicalRootReadout where
  offset : ℕ → ℤ
  life : (g : BG) → BP g → MemoryLifespanChoice (N+1)
  offset_zero : offset 0 = 0
  offset_step : ∀ i, i < N → offset (i+1)-offset i =
    sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
      (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1 (physicalAlternatingSign i) k
  support : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
    (fun i => (offset i : ZMod (bigMod g p)))
    (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N H g p) (life g p)
  before : ∀ i, i ≤ N → ∀ g, (Green64Fock.fockToList (((H.before i).2 g).2)).Perm
    (memoryCanonicalPendingList (bigMod g)
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g) (life g) offset true i)
  afterG : ∀ i, i ≤ N → ∀ g, (Green64Fock.fockToList (((H.afterG i).2 g).2)).Perm
    (memoryCanonicalPendingList (bigMod g)
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g) (life g) offset false i)
  beforeE : ∀ i, i < N → ∀ g, (Green64Fock.fockToList (((H.beforeE i).2 g).2)).Perm
    (memoryCanonicalPendingList (bigMod g)
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H g) (life g) offset false i)
  seenG : ∀ i, i ≤ N → H.seen i =
    memorySeenBeforeGValues BP bigMod
      (memorySourceWitnessActiveVisits SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig mu k N H) life i
  seenE : ∀ i, i < N →
    (H.seen i ∪ (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap
      (H.before i) (H.ghost i)).toFinset) = memoryBornBeforeValues BP bigMod life (i+1)

/-- FIRST DECISIVE UNPROVED THEOREM TARGET. No proof or custom axiom is
introduced. This target is a necessary readout bridge, not a replacement
for the original MemoryIdentityTarget or its global weighted inverse. -/
def MemorySourceCanonicalRootReadoutTarget
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (R : ℕ) : Prop :=
  ∀ hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R,
  ∀ w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R,
  Nonempty (MemorySourceCanonicalRootReadout SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R)
    (memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w))
end Green64FullPhysicalE

end

end

