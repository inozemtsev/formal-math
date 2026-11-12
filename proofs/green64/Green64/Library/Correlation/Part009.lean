module

public import Green64.Library.Correlation.Part008
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Green64.Library.Weights.Part002
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part007
public import Green64.Library.Correlation.Part006
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Correlation / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryIndRowTrueTorusShift -/

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

/-- The EXACT independent source row has deterministic Haar transport
on the COMPLETE numerical BIG and SMALL residue tori whenever the
original ν/aux/four-permutation source scalar is nonzero.
This derives both torus translations from the REAL original
permuted BIG/SMALL kernels, never from a postulated Markov law.
No condition on q, rho, or support is introduced. -/
theorem memory_ind_row_nonzero_actual_torus_translations
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hn : memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta o k x y nu aux bs bt ss st ≠ 0) :
    let delta : ℤ := o*k*
      (memoryIndependentD SP smallMod BP bigMod J ell m
        (patterns nu) aux x bs ss : ℤ)
    (∀ g : BG,
      Green64SmallHaar.residues (bigMod g) (J+ell) (y.2 g) =
      Green64SmallHaar.translate (bigMod g) delta
        (Green64SmallHaar.residues (bigMod g) (J+ell) (x.2 g))) ∧
    (∀ g : SG,
      Green64SmallHaar.residues (smallMod g) (J+ell) (y.1 g) =
      Green64SmallHaar.translate (smallMod g) delta
        (Green64SmallHaar.residues (smallMod g) (J+ell) (x.1 g))) := by
  dsimp only
  let delta : ℤ := o*k*(memoryIndependentD SP smallMod BP bigMod
    J ell m (patterns nu) aux x bs ss : ℤ)
  have hlegal : (o=1 ∨ o=-1) ∧ k ≠ 0 ∧
      memoryIndependentAuxBan SP smallMod BP bigMod J ell m
        (patterns nu) aux x y := by
    by_contra hh
    apply hn
    unfold memoryIndependentRowScalar
    simp only [hh,if_false]
  let bBig := Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
    (sourceBigShared J ell m (patterns nu)) delta
    (fun _ _ => 1) bs bt x.2 y.2
  let bSmall := Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell)
    q Vsmall (sourceSmallShared J ell) delta
    (fun _ _ => originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o nu aux
        (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i))
        (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g i)))
      zeta theta (memoryIndependentD SP smallMod BP bigMod J ell m
        (patterns nu) aux x bs ss) o k) ss st x.1 y.1
  have hbBig : bBig ≠ 0 := by
    intro hh
    apply hn
    unfold memoryIndependentRowScalar
    rw [if_pos hlegal]
    change _ * bBig * bSmall = 0
    rw [hh]
    ring
  have hbSmall : bSmall ≠ 0 := by
    intro hh
    apply hn
    unfold memoryIndependentRowScalar
    rw [if_pos hlegal]
    change _ * bBig * bSmall = 0
    rw [hh]
    ring
  have hBigAllowed : Green64SmallHaar.groupEdgeAllowedPerm BP bigMod
      (J+ell) (sourceBigShared J ell m (patterns nu))
      delta bs bt x.2 y.2 := by
    by_contra hh
    apply hbBig
    unfold bBig Green64SmallHaar.groupPermutedKernel
    simp only [hh,if_false]
  have hSmallAllowed : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod
      (J+ell) (sourceSmallShared J ell)
      delta ss st x.1 y.1 := by
    by_contra hh
    apply hbSmall
    unfold bSmall Green64SmallHaar.groupPermutedKernel
    simp only [hh,if_false]
  refine ⟨?_,?_⟩
  · intro g
    exact (hBigAllowed g).1
  · intro g
    exact (hSmallAllowed g).1
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGHaarChronology -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Transport the ENTIRE original numerical BIG torus by the same
integer displacement, not only its active marked prime coordinates. -/
def memoryIndBIGTorusTranslate (delta : ℤ)
    (c : MemoryIndependentBIGTorus BP bigMod) :
    MemoryIndependentBIGTorus BP bigMod :=
  fun g => Green64SmallHaar.translate (bigMod g) delta (c g)

/-- The original full independent BIG torus translation has exact
additive group composition, with no missing modular residue coordinate. -/
theorem memory_ind_BIG_torus_translate_comp
    (d e : ℤ) (c : MemoryIndependentBIGTorus BP bigMod) :
    memoryIndBIGTorusTranslate BP bigMod d
      (memoryIndBIGTorusTranslate BP bigMod e c) =
    memoryIndBIGTorusTranslate BP bigMod (e+d) c := by
  funext g p
  simp only [memoryIndBIGTorusTranslate,Green64SmallHaar.translate]
  push_cast
  rw [add_assoc]

theorem memory_ind_BIG_torus_translate_zero
    (c : MemoryIndependentBIGTorus BP bigMod) :
    memoryIndBIGTorusTranslate BP bigMod 0 c = c := by
  funext g p
  simp [memoryIndBIGTorusTranslate,Green64SmallHaar.translate]

/-- The exact ORIGINAL independent BIG residue path is determined at
EVERY visit by a SINGLE initial full prime torus anchor and the
chronological integer offsets, whenever each actual independent edge
enforces the source BIG translation step. The statement uses actual
full residue torus states C(t), not a postulated residue hitting law.
No normalization, stochastic independence, or active-subset quotient. -/
theorem memory_ind_BIG_torus_path_one_anchor
    (N : ℕ)
    (C : ℕ → MemoryIndependentBIGTorus BP bigMod)
    (delta offset : ℕ → ℤ)
    (hshift : ∀ t < N, C (t+1) =
      memoryIndBIGTorusTranslate BP bigMod (delta t) (C t))
    (hoff : ∀ t < N, offset (t+1)=offset t+delta t)
    (hzero : offset 0 = 0) :
    ∀ t ≤ N, C t =
      memoryIndBIGTorusTranslate BP bigMod (offset t) (C 0) := by
  intro t ht
  induction t with
  | zero =>
    rw [hzero]
    exact (memory_ind_BIG_torus_translate_zero BP bigMod (C 0)).symm
  | succ i ih =>
    have hi : i < N := Nat.lt_of_succ_le ht
    calc
      C (i+1) = memoryIndBIGTorusTranslate BP bigMod
          (delta i) (C i) := hshift i hi
      _ = memoryIndBIGTorusTranslate BP bigMod
          (delta i) (memoryIndBIGTorusTranslate BP bigMod
            (offset i) (C 0)) := by rw [ih (Nat.le_of_lt hi)]
      _ = memoryIndBIGTorusTranslate BP bigMod
          (offset (i+1)) (C 0) := by
            rw [hoff i hi]
            exact memory_ind_BIG_torus_translate_comp BP bigMod
              (delta i) (offset i) (C 0)
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGKernelPhysicalNormalization -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- The original independent BIG kernel K=1 has EXACTLY one
V_g^{-unsharedSlots} and TWO q endpoint damping factors at each BIG
group, CONDITIONAL ON its real oriented source/target permutation
and full residue translation legality. Neither original permutation
factorial is contained here; both are external in memoryIndependentRow.
No fictitious BIG independent step normalization. -/
theorem memory_ind_BIG_true_kernel_V_and_endpoint_damping
    (M : ℕ) (q : ℝ) (Vbig : BG → ℝ)
    (shared : BG → Finset (Fin M)) (delta : ℤ)
    (bs bt : Green64SmallHaar.GroupPermFamily (G := BG) M)
    (x y : Green64SmallHaar.GroupState BP bigMod M) :
    Green64SmallHaar.groupPermutedKernel BP bigMod M
      q Vbig shared delta (fun _ _ => 1) bs bt x y =
    if Green64SmallHaar.groupEdgeAllowedPerm BP bigMod M
        shared delta bs bt x y then
      (∏ g : BG, (((1:ℝ)/(Vbig g)^
        (Green64SmallHaar.unsharedSlots M (shared g)) : ℝ) : ℂ)) *
      (∏ g : BG, ((Green64SmallHaar.endpointDamping (bigMod g) M
        q (x g) *
        Green64SmallHaar.endpointDamping (bigMod g) M q (y g) : ℝ) : ℂ))
    else 0 := by
  by_cases h : Green64SmallHaar.groupEdgeAllowedPerm BP bigMod
      M shared delta bs bt x y
  · rw [if_pos h]
    unfold Green64SmallHaar.groupPermutedKernel
    rw [if_pos h]
    simp only [one_mul]
    unfold Green64SmallHaar.groupEdgeScalar Green64SmallHaar.edgeScalar
    rw [← Finset.prod_mul_distrib]
    push_cast
    apply Finset.prod_congr rfl
    intro g hg
    ring
  · rw [if_neg h]
    unfold Green64SmallHaar.groupPermutedKernel
    rw [if_neg h]
end Green64FullPhysicalE

end

end

/-! ## MemorySourceDefinitionBridge -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Forget BIG torus residues, retaining the actual source active lists and
the actual Fock vacuum. This does not assert any equality of their measures. -/
def memoryIndependentVacuumPhysical
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) :
    FullPhysicalState SP smallMod BP bigMod (J+ell) cap :=
  (x.1, fun g =>
    (Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g),
      Green64Fock.vacuumState (Green64Fock.Atom (BP g) (bigMod g)) (cap g)))

/-- The independently defined source divisor is exactly the inherited
physical divisor on the same active lists and sampled permutations. -/
theorem memory_independent_divisor_is_physical
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    memoryIndependentD SP smallMod BP bigMod J ell m pat aux x bs ss =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap pat aux
      (memoryIndependentVacuumPhysical SP smallMod BP bigMod J ell cap x) bs ss := rfl

theorem memory_reverse_kernel_arguments
    (Knu : SourcePatternK BP J ell m patterns) (nu : Nu)
    (aux : SourceBigAux BP J m (patterns nu))
    (s t : (g : BG) → Fin (J+ell) → BP g) :
    memoryOrientationK BP J ell m patterns Knu (-1) nu aux s t =
      Knu nu aux t s := by
  simp [memoryOrientationK]
end Green64FullPhysicalE

end

end

/-! ## MemorySourcePhaseAudit -/

section

open Classical
namespace Green64FullPhysicalE

/-- Exact scalar witness: assigning visit-index zero to ζ erases a source
edge phase. It does not depend on memory truncation or a numerical check. -/
theorem memory_inherited_zero_zeta (D : ℕ) :
    originalOrientedKernel 1 ((0 : ℝ) * (Real.pi / Real.log D)) D 1 = 1 := by
  simp [originalOrientedKernel]

theorem memory_true_phase_minus_one (D : ℕ) (hD : 1 < D) :
    originalOrientedKernel 1 (Real.pi / Real.log D) D 1 = -1 := by
  have hp : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_of_lt hD)
  have hl : Real.log (D : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hD))
  have hc : Complex.log (D : ℂ) = (Real.log (D : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hp.le).symm
  simp only [originalOrientedKernel, if_true, one_mul]
  rw [hc]
  have he :
      Complex.I * ((Real.pi / Real.log (D : ℝ) : ℝ) : ℂ) *
        (Real.log (D : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    rw [Complex.ofReal_div]
    have hcl : (Real.log (D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
    field_simp [hcl]
  rw [he]
  exact Complex.exp_pi_mul_I

theorem memory_spectral_schedule_scalar_issue (D : ℕ) (hD : 1 < D) :
    originalOrientedKernel 1 ((0 : ℝ) * (Real.pi / Real.log D)) D 1 ≠
      originalOrientedKernel 1 (Real.pi / Real.log D) D 1 := by
  rw [memory_inherited_zero_zeta, memory_true_phase_minus_one D hD]
  norm_num
end Green64FullPhysicalE

end

/-! ## PhysicalRawGhostFockInvariant -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- ACTUAL raw source G_i, evaluated on a symmetric Fock test,
does not depend on the OLD ordered representation. This proof
sums the original zeroOld powerset and independent fresh birth
list, reindexing ALL OLD subsets. It allows arbitrary repeated
prime-residue atoms, keeps 1/b! and uses the genuine source
GhostOperatorFinite finiteGhostG, not a quotient proxy. -/
theorem physical_raw_source_G_multiset_invariant
    {U : Type} [Fintype U] [DecidableEq U]
    (old next : List U)
    (atZero : U → Prop) [DecidablePred atZero]
    (e : Fin old.length ≃ Fin next.length)
    (h : ∀ j, old.get j = next.get (e j))
    (B : ℕ) (α χ γ : ℂ) (nu : U → ℂ)
    (F : Multiset U → ℂ) :
    Green64MemoryGhostOp.finiteGhostG old atZero B α χ γ nu
      (fun out => F (out : Multiset U)) =
    Green64MemoryGhostOp.finiteGhostG next atZero B α χ γ nu
      (fun out => F (out : Multiset U)) := by
  classical
  unfold Green64MemoryGhostOp.finiteGhostG
  have hZ := physical_ghost_zeroOld_reindex
    old next atZero e h
  have hinj : Function.Injective
      (fun A : Finset (Fin old.length) => A.image e) :=
    Finset.image_injective e.injective
  rw [← hZ, Finset.powerset_image]
  rw [Finset.sum_image (fun A _ C _ heq => hinj heq)]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro fresh hfresh
  have hweight := physical_ghost_source_term_reindex
    old next atZero e h A fresh α χ γ nu
  have hout := physical_ghost_after_multiset_reindex
    old next e h A fresh
  rw [hweight]
  exact congrArg
    (fun z : ℂ =>
      Green64MemoryGhostOp.sourceGhostTerm next atZero
        (A.image e) fresh α χ γ nu * z)
    (congrArg F hout)

end Green64FullPhysicalE

end

/-! ## PhysicalRawGhostTruncatedInvariant -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The genuinely truncated RAW G witness series is permutation-
invariant in its OLD Fock index order, including repeated atoms.
Retain the original finite-G birth cap b<=B AND the OUTPUT Fock
sector cutoff length<=B. No abstract transition law or quotient
measure replaces the source zeroOld powerset/sourceGhostTerm. -/
theorem physical_raw_G_truncated_witness_invariant
    {U : Type} [Fintype U] [DecidableEq U]
    (old next : List U)
    (atZero : U → Prop) [DecidablePred atZero]
    (e : Fin old.length ≃ Fin next.length)
    (h : ∀ j, old.get j = next.get (e j))
    (B : ℕ) (α χ γ : ℂ) (nu : U → ℂ)
    (F : Multiset U → ℂ) :
    (∑ A ∈ (Green64MemoryGhostOp.zeroOld old atZero).powerset,
      ∑ b ∈ Finset.range (B+1), ∑ fresh : Fin b → U,
        if (Green64MemoryGhostOp.afterGhost old A fresh).length ≤ B then
          Green64MemoryGhostOp.sourceGhostTerm old atZero
            A fresh α χ γ nu *
            F (Green64MemoryGhostOp.afterGhost old A fresh : Multiset U)
        else 0) =
    (∑ A ∈ (Green64MemoryGhostOp.zeroOld next atZero).powerset,
      ∑ b ∈ Finset.range (B+1), ∑ fresh : Fin b → U,
        if (Green64MemoryGhostOp.afterGhost next A fresh).length ≤ B then
          Green64MemoryGhostOp.sourceGhostTerm next atZero
            A fresh α χ γ nu *
            F (Green64MemoryGhostOp.afterGhost next A fresh : Multiset U)
        else 0) := by
  classical
  have hZ := physical_ghost_zeroOld_reindex old next atZero e h
  have hinj : Function.Injective
      (fun A : Finset (Fin old.length) => A.image e) :=
    Finset.image_injective e.injective
  rw [← hZ, Finset.powerset_image]
  rw [Finset.sum_image (fun A _ C _ heq => hinj heq)]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro fresh hfresh
  have hw := physical_ghost_source_term_reindex
    old next atZero e h A fresh α χ γ nu
  have hm := physical_ghost_after_multiset_reindex
    old next e h A fresh
  have hlen : (Green64MemoryGhostOp.afterGhost old A fresh).length =
      (Green64MemoryGhostOp.afterGhost next (A.image e) fresh).length := by
    have hc := congrArg Multiset.card hm
    simpa using hc
  rw [hw, hlen]
  exact congrArg
    (fun z : ℂ =>
      if (Green64MemoryGhostOp.afterGhost next
        (A.image e) fresh).length ≤ B then
        Green64MemoryGhostOp.sourceGhostTerm next atZero
          (A.image e) fresh α χ γ nu * z else 0)
    (congrArg F hm)

end Green64FullPhysicalE

end

/-! ## PhysicalFockStateListEquiv -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The ACTUAL source finite ordered Fock sectors are exactly all
ordered atom lists with length at most B. The 1/j! measure is NOT
part of this purely combinatorial coordinate equivalence. -/
def physicalFockStateListEquiv
    (U : Type) [Fintype U] [DecidableEq U] (B : ℕ) :
    Green64Fock.FockState U B ≃ {l : List U // l.length ≤ B} where
  toFun s := ⟨Green64Fock.fockToList s,
    by
      have h := Green64Fock.fockToList_length s
      have hbound : s.1.val ≤ B := Nat.lt_succ_iff.mp s.1.isLt
      omega⟩
  invFun l := ⟨⟨l.val.length, by omega⟩, l.val.get⟩
  left_inv := by
    rintro ⟨⟨n,hn⟩, f⟩
    apply Sigma.ext
    · apply Fin.ext
      simp [Green64Fock.fockToList]
    · have hsig :
          (⟨(List.ofFn f).length, (List.ofFn f).get⟩ :
            Σ n : ℕ, Fin n → U) = ⟨n, f⟩ :=
          (List.equivSigmaTuple (α := U)).right_inv ⟨n, f⟩
      exact (Sigma.mk.inj_iff.mp hsig).2
  right_inv := by
    rintro ⟨l, hl⟩
    apply Subtype.ext
    simp [Green64Fock.fockToList]

end Green64FullPhysicalE

end

/-! ## PhysicalGhostAnyFockPermutation -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Extend an arbitrary finite index equivalence by one distinguished
head index. This carries a list head to the same head and transports
every OLD Fock tail position. -/
def ghostFinConsEquiv {n m : ℕ}
    (e : Fin n ≃ Fin m) : Fin (n+1) ≃ Fin (m+1) :=
  (finSuccEquiv n).trans (Equiv.optionCongr e) |>.trans (finSuccEquiv m).symm

@[simp] theorem ghostFinConsEquiv_zero {n m : ℕ}
    (e : Fin n ≃ Fin m) :
    ghostFinConsEquiv e 0 = 0 := by
  simp [ghostFinConsEquiv]

@[simp] theorem ghostFinConsEquiv_succ {n m : ℕ}
    (e : Fin n ≃ Fin m) (i : Fin n) :
    ghostFinConsEquiv e i.succ = (e i).succ := by
  simp [ghostFinConsEquiv]

/-- Every multiset equality, including arbitrary repeated identical
atoms, gives an OLD-INDEX bijection preserving every individual atom.
No distinct-birth hypothesis is needed for this purely ordered
Fock reindexing: equal values have distinct OCCURRENCES. -/
theorem physical_any_multiset_old_index_equiv
    {U : Type} (left right : List U)
    (h : (left : Multiset U) = (right : Multiset U)) :
    ∃ e : Fin left.length ≃ Fin right.length,
      ∀ j, left.get j = right.get (e j) := by
  have hp : left.Perm right := Multiset.coe_eq_coe.mp h
  clear h
  induction hp with
  | nil =>
      refine ⟨Equiv.refl _, ?_⟩
      intro j
      exact Fin.elim0 j
  | @cons a x y hperm ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨ghostFinConsEquiv e, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => simp
      | succ j => simpa using he j
  | @swap a b l =>
      refine ⟨Equiv.swap 0 1, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
          cases j using Fin.cases with
          | zero => simp
          | succ k =>
              have h0 : (Fin.succ (Fin.succ k) :
                Fin (l.length + 2)) ≠ 0 := Fin.succ_ne_zero _
              have h1 : (Fin.succ (Fin.succ k) :
                Fin (l.length + 2)) ≠ 1 := Fin.succ_succ_ne_one _
              simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans p q ihp ihq =>
      obtain ⟨e, he⟩ := ihp
      obtain ⟨f, hf⟩ := ihq
      refine ⟨e.trans f, ?_⟩
      intro j
      exact (he j).trans (hf (e j))

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEFullFockSymmetry -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Raw corrected BIG-E frame row respects the genuine symmetric
Fock orbit, not just a chosen OLD permutation. Repeated identical
atoms are permitted and counted by their occurrence multiplicities.
Both independently sampled source/target frames are arbitrary. -/
theorem physical_source_oriented_E_fixed_frame_Fock_symmetry
    (mu : P → ℝ) (V rho : ℝ)
    (x y : BigState modulus M B)
    (hActive : x.1 = y.1)
    (hMemory : Green64Fock.fockMultiset x.2 =
      Green64Fock.fockMultiset y.2)
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) :
    (∑ c ∈ (Finset.univ : Finset (BigEdgeChoice modulus M B x)).filter
        (OrientedBigEdgeLegal modulus M B x target shared sigma tau D step),
        orientedBigBranchCoefficient modulus M B mu V rho
          x target shared sigma tau step c *
        F (target, physicalPendingMultiset modulus M B x sigma step c)) =
    (∑ d ∈ (Finset.univ : Finset (BigEdgeChoice modulus M B y)).filter
        (OrientedBigEdgeLegal modulus M B y target shared sigma tau D step),
        orientedBigBranchCoefficient modulus M B mu V rho
          y target shared sigma tau step d *
        F (target, physicalPendingMultiset modulus M B y sigma step d)) := by
  have hm :
      (Green64Fock.fockToList x.2 : Multiset (Green64Fock.Atom P modulus)) =
      (Green64Fock.fockToList y.2 : Multiset (Green64Fock.Atom P modulus)) := by
    simpa only [Green64Fock.fockMultiset, Green64Fock.fockToList] using hMemory
  obtain ⟨eraw, he⟩ := physical_any_multiset_old_index_equiv
    (Green64Fock.fockToList x.2)
    (Green64Fock.fockToList y.2) hm
  let hxlen : (Green64Fock.fockToList x.2).length = x.2.1.val :=
    List.length_ofFn
  let hylen : (Green64Fock.fockToList y.2).length = y.2.1.val :=
    List.length_ofFn
  let fx := finCongr hxlen.symm
  let fy := finCongr hylen
  let e : Fin x.2.1.val ≃ Fin y.2.1.val :=
    (fx.trans eraw).trans fy
  have hatoms : ∀ i, x.2.2 i = y.2.2 (e i) := by
    intro i
    have hi := he (fx i)
    have hleft :
        Fin.cast hxlen (fx i) = i := Fin.ext rfl
    have hright :
        Fin.cast hylen (eraw (fx i)) = e i := Fin.ext rfl
    have hgets :
        x.2.2 (Fin.cast hxlen (fx i)) =
          y.2.2 (Fin.cast hylen (eraw (fx i))) := by
      simpa only [Green64Fock.fockToList, List.get_ofFn] using hi
    rw [hleft, hright] at hgets
    exact hgets
  exact physical_source_oriented_E_old_fibre_weighted_sum
    modulus M B mu V rho x y e hActive hatoms
    target shared sigma tau D step F

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEOldChoiceEquiv -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Reindex the ACTUAL source BIG branch product across all groups;
each group uses its own OLD-occurrence permutation. This is a
bijection of every raw branch choice, not of its numerical prime set. -/
noncomputable def physical_oriented_big_group_old_choice_equiv
    (x y : BigGroupState BP bigMod (J+ell) cap)
    (e : (g : BG) → Fin ((x g).2.1.val) ≃ Fin ((y g).2.1.val)) :
    BigGroupBranch BP bigMod (J+ell) cap x ≃
    BigGroupBranch BP bigMod (J+ell) cap y :=
  Equiv.piCongrRight (fun g =>
    Equiv.prodCongr (Equiv.refl _)
      (physical_reindex_E_old_choice_equiv
        (bigMod g) (J+ell) (cap g) (x g) (y g) (e g)))
/-- A bijection between genuinely sampled FULL source E branches:
both BIG permutation frames and both SMALL Haar frames are kept,
as well as the actual small target state. Only indexed OLD injections
are moved groupwise. -/
noncomputable def physical_oriented_full_edge_old_choice_equiv
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val)) :
    FullPhysicalEdgeBranch SP smallMod BP bigMod (J+ell) cap x ≃
    FullPhysicalEdgeBranch SP smallMod BP bigMod (J+ell) cap y := by
  let E := physical_oriented_big_group_old_choice_equiv
    BP bigMod J ell cap x.2 y.2 e
  exact
    { toFun := fun b =>
        { sigmaBig := b.sigmaBig
          tauBig := b.tauBig
          bigChoice := E b.bigChoice
          smallTarget := b.smallTarget }
      invFun := fun b =>
        { sigmaBig := b.sigmaBig
          tauBig := b.tauBig
          bigChoice := E.symm b.bigChoice
          smallTarget := b.smallTarget }
      left_inv := by
        intro b
        cases b
        simp
      right_inv := by
        intro b
        cases b
        simp }
/-- Transport the complete original source choice: pattern nu,
independent free auxiliary draws, both groupwise BIG frames,
both SMALL permutation frames and every indexed OLD promotion. -/
noncomputable def physical_oriented_full_source_old_choice_equiv
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val)) :
    FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x ≃
    FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns y :=
  Equiv.sigmaCongrRight (fun nu =>
    Equiv.prodCongr (Equiv.refl (SourceBigAux BP J m (patterns nu)))
      (Equiv.prodCongr
        (physical_oriented_full_edge_old_choice_equiv
          SP smallMod BP bigMod J ell cap x y e)
        (Equiv.prodCongr (Equiv.refl _) (Equiv.refl _))))

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEInvariance -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The TRUE original source D depends on the SMALL state and BIG
active arrays with independently permuted source frames, not on
the ordering of OLD Fock occurrences. Includes all free C_g draws. -/
theorem physical_source_oriented_D_old_order_invariant
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (bigSigma : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      pat aux x bigSigma ss =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      pat aux y bigSigma ss := by
  simp only [sourceOrientedPhysicalD]
  congr 1
  · rw [hSmall]
  · apply Finset.prod_congr rfl
    intro g hg
    rw [hActive g]

/-- The signed step is consequently invariant under arbitrary
reindexing of OLD particles, also for the alternating - direction. -/
theorem physical_source_oriented_step_old_order_invariant
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (bigSigma : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (orientation k : ℤ) :
    sourceOrientedStep SP smallMod BP bigMod J ell m cap
      pat aux x bigSigma ss orientation k =
    sourceOrientedStep SP smallMod BP bigMod J ell m cap
      pat aux y bigSigma ss orientation k := by
  unfold sourceOrientedStep
  rw [physical_source_oriented_D_old_order_invariant
    SP smallMod BP bigMod J ell m cap
    pat aux x y hSmall hActive bigSigma ss]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEChoiceProjection -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Explicit projections of the full reindex equivalence:
nu, free D draws, all BIG and SMALL endpoint permutations and
both active targets remain IDENTICAL, while only each group OLD
index injection is transported. -/
theorem physical_oriented_full_source_old_choice_projections
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val))
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    let z' := physical_oriented_full_source_old_choice_equiv
      SP smallMod BP bigMod J ell m cap patterns x y e z
    z'.1 = z.1 ∧
    z'.2.1 = z.2.1 ∧
    z'.2.2.1.sigmaBig = z.2.2.1.sigmaBig ∧
    z'.2.2.1.tauBig = z.2.2.1.tauBig ∧
    z'.2.2.1.smallTarget = z.2.2.1.smallTarget ∧
    z'.2.2.2.1 = z.2.2.2.1 ∧
    z'.2.2.2.2 = z.2.2.2.2 ∧
    (∀ g : BG, (z'.2.2.1.bigChoice g).1 =
      (z.2.2.1.bigChoice g).1) ∧
    (∀ g : BG, (z'.2.2.1.bigChoice g).2 =
      physical_reindex_E_old_choice (bigMod g) (J+ell) (cap g)
        (x.2 g) (y.2 g) (e g) (z.2.2.1.bigChoice g).2) := by
  classical
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro g
    rfl
  · intro g
    rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullELegalReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- EXACT legal equivalence for the ORIGINAL source-oriented E,
over EVERY BIG and SMALL group, including independent endpoint
permutations, free-D bans and coupled small Haar tests. The
only operation on BIG input OLD memory is an occurrence bijection. -/
theorem physical_oriented_full_source_legal_reindex_iff
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val))
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (hAtoms : ∀ g : BG, ∀ j,
      ((x.2 g).2).2 j = ((y.2 g).2).2 (e g j))
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z ↔
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns y orientation k
        (physical_oriented_full_source_old_choice_equiv
          SP smallMod BP bigMod J ell m cap patterns x y e z) := by
  classical
  let w := physical_oriented_full_source_old_choice_equiv
    SP smallMod BP bigMod J ell m cap patterns x y e z
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let tt := z.2.2.2.2
  obtain ⟨hNu, hAux, hSig, hTau, hTarget, hSS, hTT,
      hBigTarget, hBigOld⟩ :=
    physical_oriented_full_source_old_choice_projections
      SP smallMod BP bigMod J ell m cap patterns x y e z
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss
  let delta := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss orientation k
  have hD : D = sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns w.1) w.2.1 y
      w.2.2.1.sigmaBig w.2.2.2.1 := by
    change sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux x b.sigmaBig ss =
      sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux y b.sigmaBig ss
    exact physical_source_oriented_D_old_order_invariant
      SP smallMod BP bigMod J ell m cap pat aux
      x y hSmall hActive b.sigmaBig ss
  have hDelta : delta = sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns w.1) w.2.1 y
      w.2.2.1.sigmaBig w.2.2.2.1 orientation k := by
    change sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux x b.sigmaBig ss orientation k =
      sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux y b.sigmaBig ss orientation k
    exact physical_source_oriented_step_old_order_invariant
      SP smallMod BP bigMod J ell m cap pat aux
      x y hSmall hActive b.sigmaBig ss orientation k
  have hAuxAvoid :
      sourceAuxAvoidsEndpoints SP smallMod BP bigMod
        J ell m cap pat aux x b ↔
      sourceAuxAvoidsEndpoints SP smallMod BP bigMod
        J ell m cap (patterns w.1) w.2.1 y w.2.2.1 := by
    change sourceAuxAvoidsEndpoints SP smallMod BP bigMod
        J ell m cap pat aux x b ↔
      sourceAuxAvoidsEndpoints SP smallMod BP bigMod
        J ell m cap pat aux y w.2.2.1
    constructor
    · intro hh g j i
      obtain ⟨ha, hb⟩ := hh g j i
      constructor
      · simpa only [← hActive g] using ha
      · exact hb
    · intro hh g j i
      obtain ⟨ha, hb⟩ := hh g j i
      constructor
      · simpa only [hActive g] using ha
      · exact hb
  constructor
  · intro hz
    obtain ⟨horient, hk, hAuxZ, hBigZ, hSmallZ⟩ := hz
    refine ⟨horient, hk, hAuxAvoid.mp hAuxZ, ?_, ?_⟩
    · intro g
      have hi := (physical_source_oriented_E_legal_reindex_iff
        (bigMod g) (J+ell) (cap g) (x.2 g) (y.2 g) (e g)
        (hActive g) (hAtoms g)
        (b.bigChoice g).1 (sourceBigShared J ell m pat g)
        (b.sigmaBig g) (b.tauBig g) D delta
        (b.bigChoice g).2).mp (hBigZ g)
      rw [← hD, ← hDelta]
      exact hi
    · rw [← hSmall, ← hDelta]
      exact hSmallZ
  · intro hw
    obtain ⟨horient, hk, hAuxW, hBigW, hSmallW⟩ := hw
    refine ⟨horient, hk, hAuxAvoid.mpr hAuxW, ?_, ?_⟩
    · intro g
      have hy : OrientedBigEdgeLegal (bigMod g) (J+ell)
          (cap g) (y.2 g) (b.bigChoice g).1
          (sourceBigShared J ell m pat g)
          (b.sigmaBig g) (b.tauBig g) D delta
          (physical_reindex_E_old_choice (bigMod g) (J+ell)
            (cap g) (x.2 g) (y.2 g) (e g)
            (b.bigChoice g).2) := by
        have hyraw := hBigW g
        rw [← hD, ← hDelta] at hyraw
        exact hyraw
      exact (physical_source_oriented_E_legal_reindex_iff
        (bigMod g) (J+ell) (cap g) (x.2 g) (y.2 g) (e g)
        (hActive g) (hAtoms g)
        (b.bigChoice g).1 (sourceBigShared J ell m pat g)
        (b.sigmaBig g) (b.tauBig g) D delta
        (b.bigChoice g).2).mpr hy
    · rw [← hSmall, ← hDelta] at hSmallW
      exact hSmallW

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEOutputReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Full source oriented E output is invariant under groupwise
reindexing of OLD Fock occurrences. Outputs include actual SMALL
target and every BIG active array and full Fock multiset. -/
theorem physical_oriented_full_source_output_old_reindex
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val))
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (hAtoms : ∀ g : BG, ∀ j,
      ((x.2 g).2).2 j = ((y.2 g).2).2 (e g j))
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k z =
    sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns y orientation k
      (physical_oriented_full_source_old_choice_equiv
        SP smallMod BP bigMod J ell m cap patterns x y e z) := by
  classical
  let w := physical_oriented_full_source_old_choice_equiv
    SP smallMod BP bigMod J ell m cap patterns x y e z
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let step := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss orientation k
  have hstep : step = sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns w.1) w.2.1 y
      w.2.2.1.sigmaBig w.2.2.2.1 orientation k := by
    change sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux x b.sigmaBig ss orientation k =
      sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux y b.sigmaBig ss orientation k
    exact physical_source_oriented_step_old_order_invariant
      SP smallMod BP bigMod J ell m cap pat aux
      x y hSmall hActive b.sigmaBig ss orientation k
  unfold sourceOrientedPhysicalOutput
  dsimp only
  rw [← hstep]
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · exact physical_oriented_E_pending_multiset_reindex
        (bigMod g) (J+ell) (cap g)
        (x.2 g) (y.2 g) (e g) (hActive g) (hAtoms g)
        (b.bigChoice g).2 (b.sigmaBig g) step

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEWeightReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Every complex-valued original full source E summand is preserved
under independent OLD occurrence reindexing in ALL BIG groups. Keeps
both BIG and SMALL independent permutation frames, auxiliary D and
source K_nu, D^(i zeta), Fourier, q, rho, V and mu-tilde exactly. -/
theorem physical_oriented_full_source_coefficient_old_reindex
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val))
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (hAtoms : ∀ g : BG, ∀ j,
      ((x.2 g).2).2 j = ((y.2 g).2).2 (e g j))
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k x z =
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k y
      (physical_oriented_full_source_old_choice_equiv
        SP smallMod BP bigMod J ell m cap patterns x y e z) := by
  classical
  let w := physical_oriented_full_source_old_choice_equiv
    SP smallMod BP bigMod J ell m cap patterns x y e z
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let tt := z.2.2.2.2
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss
  let delta := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss orientation k
  have hD : D = sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns w.1) w.2.1 y
      w.2.2.1.sigmaBig w.2.2.2.1 := by
    change sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux x b.sigmaBig ss =
      sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux y b.sigmaBig ss
    exact physical_source_oriented_D_old_order_invariant
      SP smallMod BP bigMod J ell m cap
      pat aux x y hSmall hActive b.sigmaBig ss
  have hDelta : delta = sourceOrientedStep SP smallMod BP bigMod
      J ell m cap (patterns w.1) w.2.1 y
      w.2.2.1.sigmaBig w.2.2.2.1 orientation k := by
    change sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux x b.sigmaBig ss orientation k =
      sourceOrientedStep SP smallMod BP bigMod
        J ell m cap pat aux y b.sigmaBig ss orientation k
    exact physical_source_oriented_step_old_order_invariant
      SP smallMod BP bigMod J ell m cap
      pat aux x y hSmall hActive b.sigmaBig ss orientation k
  have hBigProduct :
      (∏ g : BG, orientedBigBranchCoefficient
        (bigMod g) (J+ell) (cap g) (muBig g) (Vbig g) rho
        (x.2 g) (b.bigChoice g).1
        (sourceBigShared J ell m pat g)
        (b.sigmaBig g) (b.tauBig g) delta (b.bigChoice g).2) =
      (∏ g : BG, orientedBigBranchCoefficient
        (bigMod g) (J+ell) (cap g) (muBig g) (Vbig g) rho
        (y.2 g) (w.2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns w.1) g)
        (w.2.2.1.sigmaBig g) (w.2.2.1.tauBig g)
        delta (w.2.2.1.bigChoice g).2) := by
    apply Finset.prod_congr rfl
    intro g hg
    exact physical_oriented_E_branch_coefficient_reindex
      (bigMod g) (J+ell) (cap g) (muBig g) (Vbig g) rho
      (x.2 g) (y.2 g) (e g) (hActive g) (hAtoms g)
      (b.bigChoice g).1 (sourceBigShared J ell m pat g)
      (b.sigmaBig g) (b.tauBig g) delta (b.bigChoice g).2
  have hBigSourceLabels :
      (fun g i => ((x.2 g).1) (b.sigmaBig g i)) =
      (fun g i => ((y.2 g).1) (w.2.2.1.sigmaBig g i)) := by
    funext g i
    rw [hActive g]
    rfl
  unfold sourceOrientedPhysicalCoefficient
  dsimp only
  rw [← hDelta, ← hD, ← hSmall,
    ← hBigSourceLabels, ← hBigProduct]
  obtain ⟨hNu, hAux, hSig, hTau, hTarget, hSS, hTT,
      hBigTarget, hBigOld⟩ :=
    physical_oriented_full_source_old_choice_projections
      SP smallMod BP bigMod J ell m cap patterns x y e z
  simp only [hNu, hAux, hSig, hTau, hTarget, hSS, hTT,
    hBigTarget]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEWeightedSum -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exact, globally weighted source-oriented physical E sum:
all pattern, auxiliary D, BIG groups, two independent BIG and SMALL
endpoint permutation frames, OLD injections and fresh slots.
The coefficient Knu is contained once in the source coefficient. -/
theorem physical_oriented_full_source_E_weighted_old_reindex
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (e : (g : BG) →
      Fin (((x.2 g).2).1.val) ≃ Fin (((y.2 g).2).1.val))
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, ((x.2 g).1) = ((y.2 g).1))
    (hAtoms : ∀ g : BG, ∀ j,
      ((x.2 g).2).2 j = ((y.2 g).2).2 (e g j))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x F =
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k y F := by
  classical
  unfold fullSourceOrientedPhysicalE
  apply Finset.sum_equiv
    (physical_oriented_full_source_old_choice_equiv
      SP smallMod BP bigMod J ell m cap patterns x y e)
  · intro z
    simp only [sourceOrientedPhysicalChoices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact physical_oriented_full_source_legal_reindex_iff
      SP smallMod BP bigMod J ell m cap patterns
      x y e hSmall hActive hAtoms orientation k z
  · intro z hz
    rw [physical_oriented_full_source_coefficient_old_reindex
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k
      x y e hSmall hActive hAtoms z]
    rw [physical_oriented_full_source_output_old_reindex
      SP smallMod BP bigMod J ell m cap patterns
      x y e hSmall hActive hAtoms orientation k z]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEFockSymmetry -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Same finite symmetric Fock orbit gives an occurrence-level bijection,
even with repeated prime-residue atoms. This is the exact link from
unordered Fock representatives to indexed OLD promotion choices. -/
theorem physical_any_Fock_multiset_index_equiv
    {U : Type} {B : ℕ}
    (a b : Green64Fock.FockState U B)
    (h : Green64Fock.fockMultiset a =
      Green64Fock.fockMultiset b) :
    ∃ e : Fin a.1.val ≃ Fin b.1.val,
      ∀ i, a.2 i = b.2 (e i) := by
  have hm :
      (Green64Fock.fockToList a : Multiset U) =
      (Green64Fock.fockToList b : Multiset U) := by
    simpa only [Green64Fock.fockMultiset, Green64Fock.fockToList] using h
  obtain ⟨eraw, he⟩ := physical_any_multiset_old_index_equiv
    (Green64Fock.fockToList a) (Green64Fock.fockToList b) hm
  let hxlen : (Green64Fock.fockToList a).length = a.1.val :=
    List.length_ofFn
  let hylen : (Green64Fock.fockToList b).length = b.1.val :=
    List.length_ofFn
  let fx := finCongr hxlen.symm
  let fy := finCongr hylen
  let e : Fin a.1.val ≃ Fin b.1.val := (fx.trans eraw).trans fy
  refine ⟨e, ?_⟩
  intro i
  have hi := he (fx i)
  have hleft : Fin.cast hxlen (fx i) = i := Fin.ext rfl
  have hright : Fin.cast hylen (eraw (fx i)) = e i := Fin.ext rfl
  have hgets :
      a.2 (Fin.cast hxlen (fx i)) =
        b.2 (Fin.cast hylen (eraw (fx i))) := by
    simpa only [Green64Fock.fockToList, List.get_ofFn] using hi
  rw [hleft, hright] at hgets
  exact hgets

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- FULL corrected source E respects the symmetric Fock quotient.
This is the actual finite source E over ALL BIG/SMALL groups, independent
endpoint frames and arbitrary auxiliary draws, not a fixed BIG frame.
Knu occurs once, in the original sourceOrientedPhysicalCoefficient.
No distinctness or positivity assumption is needed, even for repeated atoms. -/
theorem physical_oriented_full_source_E_Fock_symmetry
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hSmall : x.1 = y.1)
    (hActive : ∀ g : BG, (x.2 g).1 = (y.2 g).1)
    (hMemory : ∀ g : BG,
      Green64Fock.fockMultiset ((x.2 g).2) =
      Green64Fock.fockMultiset ((y.2 g).2))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x F =
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k y F := by
  classical
  have hx : ∀ g : BG,
      ∃ eg : Fin (((x.2 g).2).1.val) ≃
          Fin (((y.2 g).2).1.val),
        ∀ i, ((x.2 g).2).2 i = ((y.2 g).2).2 (eg i) := by
    intro g
    exact physical_any_Fock_multiset_index_equiv
      ((x.2 g).2) ((y.2 g).2) (hMemory g)
  choose e hAtoms using hx
  exact physical_oriented_full_source_E_weighted_old_reindex
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig muBig Knu zeta theta orientation k
    x y e hSmall hActive hAtoms F

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralOldAlignment -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- At each actual G_i/E_i glue there is an OCCURRENCE-index
bijection between every BIG Fock input and G output. It
preserves both the numerical label and STORED residue, and
does not identify repeated copies of the same atom. -/
theorem physical_actual_literal_E_input_old_alignment_exists
    (i : ℕ) (hi : i < N) (g : BG) :
    ∃ e : Fin (((H.beforeE i).2 g).2).1.val ≃
        Fin (((H.afterG i).2 g).2).1.val,
      ∀ j, (((H.beforeE i).2 g).2).2 j =
        (((H.afterG i).2 g).2).2 (e j) := by
  have hp := congrArg
    (fun out : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      ((out.2 g).2)) (H.E_orbit_input i hi)
  change Green64Fock.fockMultiset (((H.beforeE i).2 g).2) =
    Green64Fock.fockMultiset (((H.afterG i).2 g).2) at hp
  exact physical_any_Fock_multiset_index_equiv
    (((H.beforeE i).2 g).2) (((H.afterG i).2 g).2) hp

/-- Concrete occurrence-level old-memory normalization map
chosen once per source BIG group; all OLD injections in E
can be transported through this map by the full E equivalence. -/
noncomputable def physicalActualLiteralOldInputEquiv
    (i : ℕ) (hi : i < N) (g : BG) :
    Fin (((H.beforeE i).2 g).2).1.val ≃
      Fin (((H.afterG i).2 g).2).1.val :=
  Classical.choose (physical_actual_literal_E_input_old_alignment_exists
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g)

/-- The actual chosen old permutation maintains the entire
prime/residue atom, hence exact OLD memory tests. -/
theorem physical_actual_literal_E_input_old_alignment
    (i : ℕ) (hi : i < N) (g : BG) (j : Fin (((H.beforeE i).2 g).2).1.val) :
    (((H.beforeE i).2 g).2).2 j =
      (((H.afterG i).2 g).2).2
        (physicalActualLiteralOldInputEquiv
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H i hi g j) :=
  Classical.choose_spec (physical_actual_literal_E_input_old_alignment_exists
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi g) j

/-- The real corrected E's output Fock is attained by an actual
ordered representative, and matches the physical state at next visit. -/
theorem physical_actual_literal_E_next_witness_projection
    (i : ℕ) (hi : i < N) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (H.before (i+1)) =
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (physicalOrientedOutputWitness SP smallMod BP bigMod
        J ell m cap patterns (H.beforeE i)
        (physicalAlternatingSign i) k (H.edge i)
        (H.E_legal i hi)) := by
  exact (H.E_output i hi).trans
    (physical_oriented_E_output_witness_correct
      SP smallMod BP bigMod J ell m cap patterns
      (H.beforeE i) (physicalAlternatingSign i) k
      (H.edge i) (H.E_legal i hi)).symm

end Green64FullPhysicalE

end

/-! ## PhysicalActualAnchorBaseline -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Averaging the zero-hit SINGLETON expansion over the original
independent uniform residue anchor gives the exact source
baseline, regardless of offset collisions. These higher-order
collisions are NOT silently discarded: they belong to the
separately required orphan ghost-history terms. -/
theorem physical_uniform_residue_linear_baseline
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (n : ℕ) :
    (∑ a : ZMod p,
      ((1 : ℝ) - ∑ i ∈ Finset.range n,
        eta i * (if h i = a then (1 : ℝ) else 0))) =
    (p : ℝ) - ∑ i ∈ Finset.range n, eta i := by
  classical
  have hdelta (i : ℕ) :
      (∑ a : ZMod p, if h i = a then (1 : ℝ) else 0) = 1 := by
    simp
  calc
    _ = (∑ a : ZMod p, (1 : ℝ)) -
          ∑ a : ZMod p, ∑ i ∈ Finset.range n,
            eta i * (if h i = a then (1 : ℝ) else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ a : ZMod p, (1 : ℝ)) -
          ∑ i ∈ Finset.range n, ∑ a : ZMod p,
            eta i * (if h i = a then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = (p : ℝ) - ∑ i ∈ Finset.range n, eta i := by
      have hon : (∑ a : ZMod p, (1 : ℝ)) = (p : ℝ) := by
        simp [ZMod.card]
      rw [hon]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      rw [hdelta i]
      ring

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- Instantiated with ALL actual signed E-edge displacements, every
visit including both source endpoints, and the original baseline
b_p (not an ad hoc zero anchor). Unrepresented primes must still
be averaged over their independent anchors; this verifies their
exact empty/singleton contribution to the original law. -/
theorem physical_actual_absent_prime_singleton_baseline
    (g : BG) (p : BP g) :
    (∑ a : ZMod (bigMod g p),
      ((1 : ℝ) - ∑ i ∈ Finset.range (N+1),
        sourceVisitEta q N i *
          (if ((physicalActualOffset SP smallMod BP bigMod
             J ell m cap patterns q rho Vbig muBig k N H i :
             ZMod (bigMod g p)) = a) then (1 : ℝ) else 0))) =
    (bigMod g p : ℝ) *
      physicalSourceBaseline BP bigMod q N g p := by
  rw [physical_uniform_residue_linear_baseline
    (bigMod g p) (sourceVisitEta q N)
    (fun i => (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g p))) (N+1)]
  unfold physicalSourceBaseline
  have hp : (bigMod g p : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne (bigMod g p)
  field_simp [hp]

end Green64FullPhysicalE

end

/-! ## PhysicalActualOrphanExpansion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Product strictly between the first hit j and the current endpoint n. -/
noncomputable def physicalOrphanTail (u : ℕ → ℝ) (j n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n, if j < t then (1 - u t) else 1

theorem physical_orphan_tail_succ (u : ℕ → ℝ) (j n : ℕ) :
    physicalOrphanTail u j (n+1) =
    physicalOrphanTail u j n * (if j < n then 1 - u n else 1) := by
  simp [physicalOrphanTail, Finset.prod_range_succ]

theorem physical_orphan_tail_forward_telescope (u : ℕ → ℝ) (j n : ℕ) :
    physicalOrphanTail u j n =
      1 - ∑ i ∈ Finset.range n,
        if j < i then u i * physicalOrphanTail u j i else 0 := by
  induction n with
  | zero =>
      simp [physicalOrphanTail]
  | succ n ih =>
      rw [physical_orphan_tail_succ, Finset.sum_range_succ]
      by_cases hj : j < n
      · simp only [if_pos hj]
        rw [ih]
        ring
      · simp only [if_neg hj]
        simpa using ih

theorem physical_orphan_tail_no_self_hit (u : ℕ → ℝ) (n : ℕ) :
    physicalOrphanTail u n (n+1) = 1 := by
  rw [physical_orphan_tail_succ]
  simp only [lt_irrefl, ↓reduceIte, mul_one]
  unfold physicalOrphanTail
  apply Finset.prod_eq_one
  intro t ht
  have htn : t < n := Finset.mem_range.mp ht
  simp [not_lt.mpr (Nat.le_of_lt htn)]

theorem physical_orphan_product_last_hit (u : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - u i)) =
      1 - ∑ j ∈ Finset.range n,
        u j * physicalOrphanTail u j n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsum :
          (∑ j ∈ Finset.range n,
            u j * physicalOrphanTail u j (n+1)) =
          (∑ j ∈ Finset.range n,
            u j * physicalOrphanTail u j n) * (1-u n) := by
        calc
          _ = ∑ j ∈ Finset.range n,
                (u j * physicalOrphanTail u j n) * (1-u n) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [physical_orphan_tail_succ]
            simp [(Finset.mem_range.mp hj), mul_assoc]
          _ = _ := by rw [Finset.sum_mul]
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      rw [hsum, physical_orphan_tail_no_self_hit, ih]
      ring

/-- Exact independent-residue average after collecting the FIRST
selected hit j. Later visits retain the true signed physical offsets,
including all possible coincidences; no anchor is fixed to zero. -/
theorem physical_uniform_anchor_orphan_last_hit
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (n : ℕ) :
    (∑ a : ZMod p,
      ∏ i ∈ Finset.range n,
        (1 - eta i * (if h i = a then (1 : ℝ) else 0))) =
    (p : ℝ) - ∑ j ∈ Finset.range n,
      eta j * physicalOrphanTail
        (fun t => eta t * (if h t = h j then (1 : ℝ) else 0)) j n := by
  classical
  let hit : ZMod p → ℕ → ℝ :=
    fun a i => eta i * (if h i = a then (1 : ℝ) else 0)
  have hsingle (j : ℕ) :
      (∑ a : ZMod p, hit a j * physicalOrphanTail (hit a) j n) =
        eta j * physicalOrphanTail (hit (h j)) j n := by
    calc
      _ = ∑ a : ZMod p,
            if h j = a then eta j * physicalOrphanTail (hit a) j n
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hj : h j = a
        · simp [hit, hj]
        · simp [hit, hj]
      _ = _ := by simp
  calc
    _ = ∑ a : ZMod p,
      ((1 : ℝ) - ∑ j ∈ Finset.range n,
        hit a j * physicalOrphanTail (hit a) j n) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact physical_orphan_product_last_hit (hit a) n
    _ = (∑ a : ZMod p, (1 : ℝ)) -
      ∑ j ∈ Finset.range n, ∑ a : ZMod p,
        hit a j * physicalOrphanTail (hit a) j n := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
    _ = (p : ℝ) - ∑ j ∈ Finset.range n,
        eta j * physicalOrphanTail (hit (h j)) j n := by
      have hon : (∑ a : ZMod p, (1 : ℝ)) = (p : ℝ) := by
        simp [ZMod.card]
      rw [hon]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => hsingle j)
    _ = _ := rfl

/-- Full ORIGINAL orphan-expansion identity for every independent
prime anchor, with the pair of first/last hits and every strictly
interior unmarked damped hit. No generic-position hypothesis, even
when offsets collide. Multiplying this by 1/p gives the source
b_p plus its exact orphan-ghost interval correction. -/
theorem physical_uniform_anchor_orphan_exact
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (n : ℕ) :
    (∑ a : ZMod p,
      ∏ t ∈ Finset.range n,
        (1 - eta t * (if h t = a then (1 : ℝ) else 0))) =
    (p : ℝ) - ∑ j ∈ Finset.range n, eta j +
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
        if j < i then
          eta j * eta i *
            (if h i = h j then (1 : ℝ) else 0) *
            physicalOrphanTail
              (fun t => eta t *
                (if h t = h j then (1 : ℝ) else 0)) j i
        else 0 := by
  have htail (j : ℕ) :
      eta j * physicalOrphanTail
        (fun t => eta t * (if h t = h j then (1 : ℝ) else 0)) j n =
      eta j - ∑ i ∈ Finset.range n,
        if j < i then
          eta j * eta i *
            (if h i = h j then (1 : ℝ) else 0) *
            physicalOrphanTail
              (fun t => eta t * (if h t = h j then (1 : ℝ) else 0)) j i
        else 0 := by
    rw [physical_orphan_tail_forward_telescope]
    simp only [mul_sub, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  calc
    _ = (p : ℝ) - ∑ j ∈ Finset.range n,
        eta j * physicalOrphanTail
          (fun t => eta t * (if h t = h j then (1 : ℝ) else 0)) j n :=
      physical_uniform_anchor_orphan_last_hit p eta h n
    _ = (p : ℝ) - ∑ j ∈ Finset.range n,
        (eta j - ∑ i ∈ Finset.range n,
          if j < i then
            eta j * eta i *
              (if h i = h j then (1 : ℝ) else 0) *
              physicalOrphanTail
                (fun t => eta t *
                  (if h t = h j then (1 : ℝ) else 0)) j i
          else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact htail j
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      ring

/-- Precisely the original independent-residue orphan expansion
after dividing by the p possible anchors: b_p and all j< i ghost
lifespans, each with its interior q/(...) damping at actual hits. -/
theorem physical_uniform_anchor_orphan_normalized
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (n : ℕ) :
    ((∑ a : ZMod p,
        ∏ t ∈ Finset.range n,
          (1 - eta t * (if h t = a then (1 : ℝ) else 0))) /
        (p : ℝ)) =
    (1 - (∑ j ∈ Finset.range n, eta j) / (p : ℝ)) +
      (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
        if j < i then
          eta j * eta i *
            (if h i = h j then (1 : ℝ) else 0) *
            physicalOrphanTail
              (fun t => eta t *
                (if h t = h j then (1 : ℝ) else 0)) j i
        else 0) / (p : ℝ) := by
  rw [physical_uniform_anchor_orphan_exact]
  have hp : (p : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne p
  field_simp [hp] <;> ring

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- FULL SOURCE orphan-expansion formula for the genuine signed
offsets of the actual finite physical G/E witness. No restriction
on multiple congruent visits. The absent BIG prime always keeps
its independent uniform anchor, and its contribution is exactly
the original physicalSourceBaseline b_p plus the complete pairwise
orphan-ghost interval correction. This closes the source
eq:orphan-expansion as a finite algebraic identity, NOT yet
the global weighted witness/history pushforward. -/
theorem physical_actual_source_absent_orphan_expansion
    (g : BG) (p : BP g) :
    let h : ℕ → ZMod (bigMod g p) :=
      fun i => (physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :
          ZMod (bigMod g p))
    ((∑ a : ZMod (bigMod g p),
      ∏ t ∈ Finset.range (N+1),
        (1 - sourceVisitEta q N t *
          (if h t = a then (1 : ℝ) else 0))) /
        (bigMod g p : ℝ)) =
      physicalSourceBaseline BP bigMod q N g p +
        (∑ j ∈ Finset.range (N+1),
          ∑ i ∈ Finset.range (N+1),
            if j < i then
              sourceVisitEta q N j * sourceVisitEta q N i *
              (if h i = h j then (1 : ℝ) else 0) *
              physicalOrphanTail
                (fun t => sourceVisitEta q N t *
                  (if h t = h j then (1 : ℝ) else 0)) j i
            else 0) / (bigMod g p : ℝ) := by
  dsimp only
  convert physical_uniform_anchor_orphan_normalized
    (bigMod g p) (sourceVisitEta q N)
    (fun i => (physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :
      ZMod (bigMod g p))) (N+1) using 1
  unfold physicalSourceBaseline
  rfl

end Green64FullPhysicalE

end

/-! ## MemoryActiveResidueExpansion -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Original frozen-path factor of one BIG prime. The active-set indicator
is inside the uniform anchor sum, including incompatible active offsets. -/
def memoryPrimeHaar (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n : ℕ) : ℝ :=
  (∑ c : ZMod p,
    if ∀ i ∈ A, h i = c then
      ∏ t ∈ Finset.range n,
        if t ∈ A then 1 else
          1 - eta t * (if h t = c then (1 : ℝ) else 0)
    else 0) / (p : ℝ)

def memoryActiveCore (u : ℕ → ℝ) (A : Finset ℕ)
    (a z n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n,
    if a < t ∧ t < z ∧ t ∉ A then 1-u t else 1

/-- A first active hit fixes the independent anchor once, at cost 1/p.
All remaining marked visits are tested against that same anchor. -/
theorem memory_active_anchor_collapse (p : ℕ) [NeZero p]
    (eta : ℕ → ℝ) (h : ℕ → ZMod p) (A : Finset ℕ)
    (n a : ℕ) (ha : a ∈ A) :
    memoryPrimeHaar p eta h A n =
      if ∀ i ∈ A, h i = h a then
        (∏ t ∈ Finset.range n,
          if t ∈ A then 1 else
            1 - eta t * (if h t = h a then (1 : ℝ) else 0)) / (p : ℝ)
      else 0 := by
  unfold memoryPrimeHaar
  have hs :
      (∑ c : ZMod p,
        if ∀ i ∈ A, h i = c then
          ∏ t ∈ Finset.range n,
            if t ∈ A then 1 else
              1 - eta t * (if h t = c then (1 : ℝ) else 0)
        else 0) =
      if ∀ i ∈ A, h i = h a then
        ∏ t ∈ Finset.range n,
          if t ∈ A then 1 else
            1 - eta t * (if h t = h a then (1 : ℝ) else 0)
      else 0 := by
    apply Finset.sum_eq_single (h a)
    · intro c hc hca
      have hn : ¬ ∀ i ∈ A, h i = c := by
        intro hh
        exact hca (hh a ha).symm
      simp [hn]
    · simp
  rw [hs]
  split_ifs <;> simp

/-- Every inactive factor splits uniquely into before-first, internal, and
after-last visits. Both active endpoint factors are exactly one. -/
theorem memory_active_product_split (u : ℕ → ℝ) (A : Finset ℕ)
    (n a z : ℕ) (haz : a ≤ z) (hzn : z < n)
    (ha : a ∈ A) (hz : z ∈ A)
    (hbound : ∀ t ∈ A, a ≤ t ∧ t ≤ z) :
    (∏ t ∈ Finset.range n, if t ∈ A then (1 : ℝ) else 1-u t) =
      (∏ t ∈ Finset.range a, (1-u t)) *
      memoryActiveCore u A a z n * physicalOrphanTail u z n := by
  have hp (t : ℕ) (ht : t < n) :
      (if t ∈ A then (1 : ℝ) else 1-u t) =
        (if t < a then 1-u t else 1) *
        (if a < t ∧ t < z ∧ t ∉ A then 1-u t else 1) *
        (if z < t then 1-u t else 1) := by
    by_cases hta : t < a
    · have hn : t ∉ A := by
        intro hm
        have hb := (hbound t hm).1
        omega
      have hzt : ¬ z < t := by omega
      simp [hta, hn, hzt, not_lt.mpr (Nat.le_of_lt hta)]
    · by_cases hzt : z < t
      · have hn : t ∉ A := by
          intro hm
          have hb := (hbound t hm).2
          omega
        have htz : ¬ t < z := by omega
        simp [hta, hzt, htz, hn]
      · by_cases hm : t ∈ A
        · simp [hm, hta, hzt]
        · have hat : a < t := by
            by_contra hh
            have he : t = a := by omega
            subst t
            exact hm ha
          have htz : t < z := by
            by_contra hh
            have he : t = z := by omega
            subst t
            exact hm hz
          simp [hm, hta, hzt, hat, htz]
  have hpre :
      (∏ t ∈ Finset.range n, if t < a then 1-u t else 1) =
      ∏ t ∈ Finset.range a, (1-u t) := by
    have han : a ≤ n := by omega
    rw [← Finset.prod_subset (Finset.range_mono han)
      (f := fun t => if t < a then 1-u t else 1)]
    · apply Finset.prod_congr rfl
      intro t ht
      simp [Finset.mem_range.mp ht]
    · intro t htn hta
      simp only [Finset.mem_range] at hta
      simp [hta]
  calc
    _ = ∏ t ∈ Finset.range n,
      (if t < a then 1-u t else 1) *
      (if a < t ∧ t < z ∧ t ∉ A then 1-u t else 1) *
      (if z < t then 1-u t else 1) := by
        apply Finset.prod_congr rfl
        intro t ht
        exact hp t (Finset.mem_range.mp ht)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hpre]
      rfl

def memoryPrefixChoice (u : ℕ → ℝ) (a j : ℕ) : ℝ :=
  if j = a then 1 else -u j * physicalOrphanTail u j a

def memorySuffixChoice (u : ℕ → ℝ) (z i : ℕ) : ℝ :=
  if i = z then 1 else
    if z < i then -u i * physicalOrphanTail u z i else 0

theorem memory_prefix_choices_complete (u : ℕ → ℝ) (a : ℕ) :
    (∏ t ∈ Finset.range a, (1-u t)) =
      ∑ j ∈ Finset.range (a+1), memoryPrefixChoice u a j := by
  rw [Finset.sum_range_succ]
  have hh :
      (∑ j ∈ Finset.range a, memoryPrefixChoice u a j) =
      -(∑ j ∈ Finset.range a, u j * physicalOrphanTail u j a) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hja : j ≠ a := Nat.ne_of_lt (Finset.mem_range.mp hj)
    simp [memoryPrefixChoice, hja]
  rw [hh]
  simp only [memoryPrefixChoice, if_true]
  rw [physical_orphan_product_last_hit]
  ring

theorem memory_suffix_choices_complete (u : ℕ → ℝ) (z n : ℕ) (hzn : z < n) :
    physicalOrphanTail u z n =
      ∑ i ∈ Finset.range n, memorySuffixChoice u z i := by
  rw [physical_orphan_tail_forward_telescope]
  have hterm (i : ℕ) :
      memorySuffixChoice u z i =
        (if i = z then (1 : ℝ) else 0) -
        (if z < i then u i * physicalOrphanTail u z i else 0) := by
    by_cases hiz : i = z
    · simp [memorySuffixChoice, hiz]
    · by_cases hzi : z < i <;> simp [memorySuffixChoice, hiz, hzi]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp [hzn]

/-- Complete source represented-prime expansion, with EVERY earlier ghost
birth and later ghost termination. No chosen-lifespan or surjectivity
hypothesis. Collision offsets are retained in u(t)=η(t)·1[h(t)=h(a)]. -/
theorem memory_active_haar_all_endpoints
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n a z : ℕ)
    (haz : a ≤ z) (hzn : z < n)
    (ha : a ∈ A) (hz : z ∈ A)
    (hbound : ∀ t ∈ A, a ≤ t ∧ t ≤ z) :
    memoryPrimeHaar p eta h A n =
      if ∀ t ∈ A, h t = h a then
        ∑ j ∈ Finset.range (a+1), ∑ i ∈ Finset.range n,
          memoryPrefixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) a j *
          memoryActiveCore (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) A a z n *
          memorySuffixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) z i /
          (p : ℝ)
      else 0 := by
  rw [memory_active_anchor_collapse p eta h A n a ha]
  split_ifs
  · let u : ℕ → ℝ := fun t => eta t * (if h t = h a then (1 : ℝ) else 0)
    rw [memory_active_product_split u A n a z haz hzn ha hz hbound,
      memory_prefix_choices_complete u a, memory_suffix_choices_complete u z n hzn]
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
  · rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteLifespanExpansion -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

theorem memory_sum_fin_pair (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j : Fin n, ∑ i : Fin n, f j.val i.val) =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n, f j i := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ i : Fin n, f j i.val) n]
  apply Finset.sum_congr rfl
  intro j hj
  exact Fin.sum_univ_eq_sum_range (f j) n

/-- Finite numerical lifespan choices. none is the absent baseline sector;
a pair is one birth/termination interval. No repeated copy of a prime. -/
abbrev MemoryLifespanChoice (n : ℕ) := Option (Fin n × Fin n)

def memoryOrphanInterval (p : ℕ) (eta : ℕ → ℝ)
    {n : ℕ} (h : ℕ → ZMod p) (ji : Fin n × Fin n) : ℝ :=
  if ji.1.val < ji.2.val then
    eta ji.1.val * eta ji.2.val *
      (if h ji.2.val = h ji.1.val then (1 : ℝ) else 0) *
      physicalOrphanTail
        (fun t => eta t * (if h t = h ji.1.val then (1 : ℝ) else 0))
        ji.1.val ji.2.val / (p : ℝ)
  else 0

def memoryAbsentTerm (p : ℕ) (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (n : ℕ) : MemoryLifespanChoice n → ℝ
  | none => 1 - (∑ t ∈ Finset.range n, eta t) / (p : ℝ)
  | some ji => memoryOrphanInterval p eta h ji

theorem memory_absent_all_lifespans (p : ℕ) [NeZero p]
    (eta : ℕ → ℝ) (h : ℕ → ZMod p) (n : ℕ) :
    memoryPrimeHaar p eta h ∅ n =
      ∑ l : MemoryLifespanChoice n, memoryAbsentTerm p eta h n l := by
  rw [Fintype.sum_option]
  simp only [memoryAbsentTerm]
  rw [Fintype.sum_prod_type]
  simp only [memoryOrphanInterval]
  rw [memory_sum_fin_pair (fun j i => if j < i then
    eta j * eta i * (if h i = h j then (1 : ℝ) else 0) *
    physicalOrphanTail (fun t => eta t * (if h t = h j then (1 : ℝ) else 0)) j i /
    (p : ℝ) else 0) n]
  simpa [memoryPrimeHaar, Finset.sum_div, ite_div] using
    (physical_uniform_anchor_orphan_normalized p eta h n)

def memoryRepresentedTerm (p : ℕ) (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n a z : ℕ) :
    MemoryLifespanChoice n → ℝ
  | none => 0
  | some ji =>
      if (∀ t ∈ A, h t = h a) ∧ ji.1.val ≤ a then
        memoryPrefixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) a ji.1.val *
        memoryActiveCore (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) A a z n *
        memorySuffixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) z ji.2.val /
        (p : ℝ)
      else 0

/-- All represented-prime source intervals as a single finite lifespan sum.
Missing/incompatible terms have coefficient zero, rather than being assumed
to have a root occurrence. -/
theorem memory_represented_all_lifespans
    (p : ℕ) [NeZero p] (eta : ℕ → ℝ)
    (h : ℕ → ZMod p) (A : Finset ℕ) (n a z : ℕ)
    (haz : a ≤ z) (hzn : z < n)
    (ha : a ∈ A) (hz : z ∈ A)
    (hbound : ∀ t ∈ A, a ≤ t ∧ t ≤ z) :
    memoryPrimeHaar p eta h A n =
      ∑ l : MemoryLifespanChoice n, memoryRepresentedTerm p eta h A n a z l := by
  rw [memory_active_haar_all_endpoints p eta h A n a z haz hzn ha hz hbound]
  rw [Fintype.sum_option]
  simp only [memoryRepresentedTerm, zero_add]
  rw [Fintype.sum_prod_type]
  rw [memory_sum_fin_pair (fun j i =>
    if (∀ t ∈ A, h t = h a) ∧ j ≤ a then
      memoryPrefixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) a j *
      memoryActiveCore (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) A a z n *
      memorySuffixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) z i /
      (p : ℝ) else 0) n]
  by_cases hc : ∀ t ∈ A, h t = h a
  · simp only [show (∀ t ∈ A, h t = h a) ↔ True from iff_true_intro hc, true_and, if_true]
    have han : a+1 ≤ n := by omega
    rw [← Finset.sum_subset (Finset.range_mono han)
      (f := fun j => ∑ i ∈ Finset.range n,
        if j ≤ a then
          memoryPrefixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) a j *
          memoryActiveCore (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) A a z n *
          memorySuffixChoice (fun t => eta t * (if h t = h a then (1 : ℝ) else 0)) z i /
          (p : ℝ)
        else 0)]
    · apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ a := by have := Finset.mem_range.mp hj; omega
      simp only [hjle, if_true]
    · intro j hjn hja
      have hjnot : ¬ j ≤ a := by
        simp only [Finset.mem_range] at hja
        omega
      simp only [hjnot, if_false, Finset.sum_const_zero]
  · simp only [show (∀ t ∈ A, h t = h a) ↔ False from iff_false_intro hc, false_and, if_false, Finset.sum_const_zero]
end Green64FullPhysicalE

end

end

/-! ## PhysicalOrientedFullEQuotientInput -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Physical Fock quotient equality is exactly the datum needed
to apply the complete source E invariance theorem. -/
theorem physical_oriented_full_E_eq_of_projected_input
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hxy : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap y)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x F =
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k y F := by
  have hSmall : x.1 = y.1 :=
    congrArg (fun z : FullPhysicalOutput SP smallMod BP bigMod
      (J+ell) => z.1) hxy
  have hBig : (fun g => ((x.2 g).1,
      Green64Fock.fockMultiset ((x.2 g).2))) =
    (fun g => ((y.2 g).1,
      Green64Fock.fockMultiset ((y.2 g).2))) :=
    congrArg (fun z : FullPhysicalOutput SP smallMod BP bigMod
      (J+ell) => z.2) hxy
  have hActive : ∀ g : BG, (x.2 g).1 = (y.2 g).1 := by
    intro g
    exact congrArg (fun ab : (Fin (J+ell) → BP g) ×
      Multiset (Green64Fock.Atom (BP g) (bigMod g)) => ab.1)
      (congrFun hBig g)
  have hMemory : ∀ g : BG,
      Green64Fock.fockMultiset ((x.2 g).2) =
        Green64Fock.fockMultiset ((y.2 g).2) := by
    intro g
    exact congrArg (fun ab : (Fin (J+ell) → BP g) ×
      Multiset (Green64Fock.Atom (BP g) (bigMod g)) => ab.2)
      (congrFun hBig g)
  exact physical_oriented_full_source_E_Fock_symmetry
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig muBig Knu zeta theta orientation k
    x y hSmall hActive hMemory F


end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullEProjectionAverage -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- On the genuine positive symmetric Fock Hilbert space,
the corrected FULL E preserves each Fock input fibre. Therefore
the actual weighted orthogonal quotient agrees pointwise with
the unaveraged corrected E, without any extra Knu or factorial. -/
theorem physical_symmetric_oriented_E_eq_unaveraged
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    physicalSymmetricOrientedE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x) F =
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x F := by
  classical
  let y := physicalFockProjection SP smallMod BP bigMod (J+ell) cap x
  let S := actualPhysicalInputFibre SP smallMod BP bigMod
    (J+ell) cap y
  have hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod
      (J+ell) cap :=
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hdis := physical_oriented_exact_Fock_fibre_disintegration
    SP smallMod BP bigMod (J+ell) cap Vsmall muBig hV hmu
    y hy (fun u => fullSourceOrientedPhysicalE
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k u F)
  have hconst : ∀ u ∈ S,
      fullSourceOrientedPhysicalE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k u F =
      fullSourceOrientedPhysicalE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x F := by
    intro u hu
    exact physical_oriented_full_E_eq_of_projected_input
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k
      u x (Finset.mem_filter.mp hu).2 F
  have hsum :
      (∑ u ∈ S, fullSourceOrientedPhysicalE
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig muBig Knu zeta theta orientation k
        u F) =
      (S.card : ℂ) * fullSourceOrientedPhysicalE
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig muBig Knu zeta theta orientation k x F := by
    calc
      _ = ∑ u ∈ S, fullSourceOrientedPhysicalE
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig muBig Knu zeta theta orientation k x F :=
          Finset.sum_congr rfl (fun u hu => hconst u hu)
      _ = _ := by simp
  have hcard : (S.card : ℂ) ≠ 0 := by
    have hx : x ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨x, hx⟩)
  change (∑ u ∈ S,
      (fullPhysicalMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig u : ℂ) *
      fullSourceOrientedPhysicalE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k u F) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J+ell) cap Vsmall muBig y : ℂ) =
      fullSourceOrientedPhysicalE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x F
  rw [hdis, hsum]
  dsimp only [S] at hcard
  field_simp [hcard]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalRawWitnessUnrolling -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- A REAL finite physical Hilbert orbit average is the weighted
sum of its original ordered physical Fock representatives.
Even unreachable or zero-mass output orbits obey this algebraic
identity: no positivity or invented Markov transition is assumed. -/
theorem fullPhysicalOrbitAverage_fibre_formula
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (h : FullPhysicalState SP smallMod BP bigMod M cap → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod M) :
    fullPhysicalOrbitAverage SP smallMod BP bigMod M cap
      Vsmall muBig h y =
    ∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod M cap)) with
        physicalFockProjection SP smallMod BP bigMod M cap x = y,
      ((fullPhysicalMass SP smallMod BP bigMod M cap
        Vsmall muBig x : ℂ) /
       (physicalOrbitMass SP smallMod BP bigMod M cap
        Vsmall muBig y : ℂ)) * h x := by
  classical
  unfold fullPhysicalOrbitAverage
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalFullGEWitnessExpansion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- One complete SOURCE G_i E_i pair, expanded BEFORE grouping
any ghost or E witnesses. This formula exposes every genuine
physical Hilbert input fibre, old-zero/fresh ghost witness,
source pattern+auxiliary-D choice, OLD promotion and fresh-E
birth, with its chronological global prime birth marker.
The denominators are the derived Fock orbit masses. -/
theorem fullPhysicalGE_witness_expansion
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP smallMod BP bigMod
        J ell cap q rho N i Vsmall Vbig muBig y seen
        (fun yg sg =>
          physicalMarkedSymmetricE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k yg sg F) =
    ∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J + ell) cap x = y,
      ((fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) /
       (physicalOrbitMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig y : ℂ)) *
      (∑ yg : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
        ∑ c : FullGhostWitness SP smallMod BP bigMod
            (J + ell) cap x,
          if physicalGhostBatchEligible SP smallMod BP bigMod
              (J + ell) cap x seen c then
            physicalGBranchTerm SP smallMod BP bigMod
              (J + ell) cap q rho N i Vbig muBig x yg c *
            (∑ xe ∈ (Finset.univ : Finset
                (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
                with physicalFockProjection SP smallMod BP bigMod
                  (J + ell) cap xe =
                  physicalFockProjection SP smallMod BP bigMod
                    (J + ell) cap yg,
              ((fullPhysicalMass SP smallMod BP bigMod
                (J + ell) cap Vsmall muBig xe : ℂ) /
               (physicalOrbitMass SP smallMod BP bigMod
                (J + ell) cap Vsmall muBig
                (physicalFockProjection SP smallMod BP bigMod
                  (J + ell) cap yg) : ℂ)) *
              (∑ z ∈ legalSourcePhysicalChoices SP smallMod BP bigMod
                  J ell m cap patterns xe orientation k,
                if physicalFreshBatchEligible SP smallMod BP bigMod
                    J ell m cap patterns
                    (seen ∪ (physicalGhostFreshBirths SP smallMod
                      BP bigMod (J + ell) cap x c).toFinset) z then
                  sourcePhysicalCoefficient SP smallMod BP bigMod
                    J ell m cap patterns q rho Vsmall Vbig muBig
                    Knu zeta theta orientation k xe z *
                  F (sourcePhysicalOutput SP smallMod BP bigMod
                    J ell m cap patterns xe orientation k z)
                    ((seen ∪ (physicalGhostFreshBirths SP smallMod
                      BP bigMod (J + ell) cap x c).toFinset) ∪
                      (physicalEFreshBirths SP smallMod BP bigMod
                        J ell m cap patterns z).toFinset)
                else 0))
          else 0) := by
  classical
  unfold physicalMarkedSymmetricG physicalMarkedSymmetricE
  simp only [fullPhysicalOrbitAverage_fibre_formula,
    physicalGBirthMarkedRow, physicalBirthMarkedE]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedGEExpansion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- A complete single visit and immediately following edge, expanded
into actual original G old/ghost witnesses, BOTH weighted physical
Fock representative fibres, and the NEW permutation-correct ν,D,E
source choices. No postulated Markov kernel replaces a witness. -/
theorem fullOrientedGE_witness_expansion
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP smallMod BP bigMod
        J ell cap q rho N i Vsmall Vbig muBig y seen
        (fun yg sg =>
          physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k yg sg F) =
    ∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J + ell) cap x = y,
      ((fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) /
       (physicalOrbitMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig y : ℂ)) *
      (∑ yg : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
        ∑ c : FullGhostWitness SP smallMod BP bigMod
            (J + ell) cap x,
          if physicalGhostBatchEligible SP smallMod BP bigMod
              (J + ell) cap x seen c then
            physicalGBranchTerm SP smallMod BP bigMod
              (J + ell) cap q rho N i Vbig muBig x yg c *
            (∑ xe ∈ (Finset.univ : Finset
                (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
                with physicalFockProjection SP smallMod BP bigMod
                  (J + ell) cap xe =
                  physicalFockProjection SP smallMod BP bigMod
                    (J + ell) cap yg,
              ((fullPhysicalMass SP smallMod BP bigMod
                (J + ell) cap Vsmall muBig xe : ℂ) /
               (physicalOrbitMass SP smallMod BP bigMod
                (J + ell) cap Vsmall muBig
                (physicalFockProjection SP smallMod BP bigMod
                  (J + ell) cap yg) : ℂ)) *
              (∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
                  J ell m cap patterns xe orientation k,
                if orientedEFreshBatchEligible SP smallMod BP bigMod
                    J ell m cap patterns
                    (seen ∪ (physicalGhostFreshBirths SP smallMod
                      BP bigMod (J + ell) cap x c).toFinset) z then
                  sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
                    J ell m cap patterns q rho Vsmall Vbig muBig
                    Knu zeta theta orientation k xe z *
                  F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
                    J ell m cap patterns xe orientation k z)
                    ((seen ∪ (physicalGhostFreshBirths SP smallMod
                      BP bigMod (J + ell) cap x c).toFinset) ∪
                      (orientedEFreshBirths SP smallMod BP bigMod
                        J ell m cap patterns z).toFinset)
                else 0))
          else 0) := by
  classical
  unfold physicalMarkedSymmetricG
    physicalOrientedMarkedSymmetricE
  simp only [fullPhysicalOrbitAverage_fibre_formula,
    physicalGBirthMarkedRow, physicalOrientedBirthMarkedE]

end Green64FullPhysicalE

end

/-! ## PhysicalRawWitnessChain -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Raw visit witness expansion: each actual ordered source Fock
representative has its inherited weight; the G row still sums
concrete old-zero and new-ghost witnesses with the global marker. -/
noncomputable def physicalRawWitnessVisit
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap)) with
      physicalFockProjection SP smallMod BP bigMod (J + ell) cap x = y,
    ((fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) /
     (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ)) *
    physicalGBirthMarkedRow SP smallMod BP bigMod
      (J + ell) cap q rho N i Vbig muBig x seen F

/-- One raw physical SOURCE G_i,E_i pair; no invented transition
kernel. The G and E rows here contain the complete original
physical old/fresh witness and ν/auxiliary-D branch enumerations.
Both actual Fock input orbit masses appear exactly once. -/
noncomputable def physicalRawWitnessGE
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap)) with
      physicalFockProjection SP smallMod BP bigMod (J + ell) cap x = y,
    ((fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) /
     (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ)) *
    physicalGBirthMarkedRow SP smallMod BP bigMod
      (J + ell) cap q rho N i Vbig muBig x seen
      (fun yg seenG =>
        ∑ xe ∈ (Finset.univ : Finset
          (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
          with physicalFockProjection SP smallMod BP bigMod
            (J + ell) cap xe = yg,
          ((fullPhysicalMass SP smallMod BP bigMod
            (J + ell) cap Vsmall muBig xe : ℂ) /
           (physicalOrbitMass SP smallMod BP bigMod
             (J + ell) cap Vsmall muBig yg : ℂ)) *
          physicalBirthMarkedE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k xe seenG F)

/-- Direct equality to the genuinely physical G_i row. -/
theorem physicalRawWitnessVisit_eq_source
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) :
    physicalRawWitnessVisit SP smallMod BP bigMod
      J ell cap q rho N i Vsmall Vbig muBig F y seen =
    physicalMarkedSymmetricG SP smallMod BP bigMod
      J ell cap q rho N i Vsmall Vbig muBig y seen F := by
  unfold physicalRawWitnessVisit physicalMarkedSymmetricG
  simp only [fullPhysicalOrbitAverage_fibre_formula]

/-- Exact one-edge identification of the full raw physical
witness pair with G_i E_i, including BOTH Fock orbit fibres
and the global chronological birth-set updates. -/
theorem physicalRawWitnessGE_eq_source
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) :
    physicalRawWitnessGE SP smallMod BP bigMod J ell m cap
      patterns q rho N i Vsmall Vbig muBig
      Knu zeta theta orientation k F y seen =
    physicalMarkedSymmetricG SP smallMod BP bigMod
        J ell cap q rho N i Vsmall Vbig muBig y seen
        (fun yg sg =>
          physicalMarkedSymmetricE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k yg sg F) := by
  unfold physicalRawWitnessGE physicalMarkedSymmetricG
    physicalMarkedSymmetricE
  simp only [fullPhysicalOrbitAverage_fibre_formula]

/-- The complete source-indexed path is now a recursive sum
over original physical ghost witnesses and real pattern/free-D
E choices, with ONE global accumulated numerical birth-set.
This is a raw physical path sum, not a postulated Markov chain. -/
noncomputable def physicalRawWitnessGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
  | 0, start, F =>
      physicalRawWitnessVisit SP smallMod BP bigMod
        J ell cap q rho N start Vsmall Vbig muBig F
  | remaining + 1, start, F =>
      physicalRawWitnessGE SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ) * zeta) theta
        (physicalAlternatingSign start) k
        (physicalRawWitnessGEChain q rho Vsmall Vbig muBig
          Knu zeta theta k N remaining (start + 1) F)

/-- All finite times, not just one edge: the previously compressed
source-marked root chain equals the explicit raw witness path sum.
Every original G/E coefficient survives with its Hilbert mass,
and birth uniqueness is tested on the full chronological history. -/
theorem physicalMarkedGEChain_eq_rawWitnessPath
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N remaining start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) :
    physicalMarkedGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta k N remaining start F y seen =
    physicalRawWitnessGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta k N remaining start F y seen := by
  induction remaining generalizing start y seen with
  | zero =>
      exact (physicalRawWitnessVisit_eq_source SP smallMod
        BP bigMod J ell cap q rho N start
        Vsmall Vbig muBig F y seen).symm
  | succ r ih =>
      have hfun :
        physicalMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F =
        physicalRawWitnessGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F := by
        funext y' seen'
        exact ih (start + 1) y' seen'
      change
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig y seen
          (fun yg sg =>
            physicalMarkedSymmetricE SP smallMod BP bigMod
              J ell m cap patterns q rho Vsmall Vbig muBig
              Knu ((start : ℝ) * zeta) theta
                (physicalAlternatingSign start) k yg sg
              (physicalMarkedGEChain SP smallMod BP bigMod
                J ell m cap patterns q rho Vsmall Vbig muBig
                Knu zeta theta k N r (start + 1) F)) =
        physicalRawWitnessGE SP smallMod BP bigMod
          J ell m cap patterns q rho N start Vsmall Vbig muBig
          Knu ((start : ℝ) * zeta) theta
            (physicalAlternatingSign start) k
          (physicalRawWitnessGEChain SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta k N r (start + 1) F) y seen
      rw [← physicalRawWitnessGE_eq_source
        SP smallMod BP bigMod J ell m cap patterns q rho
        N start Vsmall Vbig muBig Knu
        ((start : ℝ) * zeta) theta
        (physicalAlternatingSign start) k
        (physicalMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F) y seen]
      rw [hfun]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRawChain -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- This is the complete original physical G/E witness sum with
the corrected oriented E and the TWO genuine input Hilbert Fock
masses, BEFORE projecting the adjacent memory states. -/
noncomputable def physicalOrientedRawWitnessGE
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap)) with
      physicalFockProjection SP smallMod BP bigMod (J + ell) cap x = y,
    ((fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) /
     (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ)) *
    physicalGBirthMarkedRow SP smallMod BP bigMod
      (J + ell) cap q rho N i Vbig muBig x seen
      (fun yg seenG =>
        ∑ xe ∈ (Finset.univ : Finset
          (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
          with physicalFockProjection SP smallMod BP bigMod
            (J + ell) cap xe = yg,
          ((fullPhysicalMass SP smallMod BP bigMod
            (J + ell) cap Vsmall muBig xe : ℂ) /
           (physicalOrbitMass SP smallMod BP bigMod
             (J + ell) cap Vsmall muBig yg : ℂ)) *
          physicalOrientedBirthMarkedE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k xe seenG F)

/-- Identifies the corrected genuine source G_i E_i product with
its expanded original-physical-witness expression. -/
theorem physicalOrientedRawWitnessGE_eq_source
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) :
    physicalOrientedRawWitnessGE SP smallMod BP bigMod
      J ell m cap patterns q rho N i Vsmall Vbig muBig
      Knu zeta theta orientation k F y seen =
    physicalMarkedSymmetricG SP smallMod BP bigMod
        J ell cap q rho N i Vsmall Vbig muBig y seen
        (fun yg sg =>
          physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta orientation k yg sg F) := by
  unfold physicalOrientedRawWitnessGE physicalMarkedSymmetricG
    physicalOrientedMarkedSymmetricE
  simp only [fullPhysicalOrbitAverage_fibre_formula]

/-- N+1 genuine visits G_0,...,G_N separated by N corrected
source E_i, retaining the birth-set state at EVERY witness step. -/
noncomputable def physicalOrientedRawWitnessGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
  | 0, start, F =>
      physicalRawWitnessVisit SP smallMod BP bigMod
        J ell cap q rho N start Vsmall Vbig muBig F
  | remaining + 1, start, F =>
      physicalOrientedRawWitnessGE SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ) * zeta) theta
        (physicalAlternatingSign start) k
        (physicalOrientedRawWitnessGEChain q rho Vsmall Vbig
          muBig Knu zeta theta k N remaining (start + 1) F)

/-- Source-corrected physical marked G/E = literal raw
physical witness chain for arbitrary finite R, proved by induction
without assuming a lifespan-law equivalence or Markov surrogate. -/
theorem physicalOrientedMarkedGEChain_eq_raw
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N remaining start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ) :
    physicalOrientedMarkedGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta k N remaining start F y seen =
    physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta k N remaining start F y seen := by
  induction remaining generalizing start y seen with
  | zero =>
      exact (physicalRawWitnessVisit_eq_source SP smallMod
        BP bigMod J ell cap q rho N start
        Vsmall Vbig muBig F y seen).symm
  | succ r ih =>
      have hfun :
        physicalOrientedMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F =
        physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F := by
        funext yy ss
        exact ih (start + 1) yy ss
      change
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig y seen
          (fun yg sg =>
            physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
              J ell m cap patterns q rho Vsmall Vbig muBig
              Knu ((start : ℝ) * zeta) theta
                (physicalAlternatingSign start) k yg sg
              (physicalOrientedMarkedGEChain SP smallMod BP bigMod
                J ell m cap patterns q rho Vsmall Vbig muBig
                Knu zeta theta k N r (start + 1) F)) =
        physicalOrientedRawWitnessGE SP smallMod BP bigMod
          J ell m cap patterns q rho N start Vsmall Vbig muBig
          Knu ((start : ℝ) * zeta) theta
            (physicalAlternatingSign start) k
          (physicalOrientedRawWitnessGEChain SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            Knu zeta theta k N r (start + 1) F) y seen
      rw [← physicalOrientedRawWitnessGE_eq_source
        SP smallMod BP bigMod J ell m cap patterns q rho
        N start Vsmall Vbig muBig Knu
        ((start : ℝ) * zeta) theta
        (physicalAlternatingSign start) k
        (physicalOrientedMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig
          Knu zeta theta k N r (start + 1) F) y seen]
      rw [hfun]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEIndexedWitnessExpansion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (orientation k : ℤ)

/-- An actual source-oriented E fibre INDEX includes the concrete
ordered physical Fock representative and all original E choices,
including independent BIG and SMALL sigma/tau permutations, ν/free-D,
OLD injections, independent fresh target slots and target SMALL Haar.

Legality and the global seen-birth condition are applied to the
indexed choice, never to the projected multiset or numerical prime
support. -/
noncomputable def physicalOrientedEIndexedLegalFibre
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    Finset (Σ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullOrientedSourceChoice SP smallMod BP bigMod
        J ell m cap patterns x) :=
  Finset.univ.filter (fun a =>
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.1 = y ∧
    sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns a.1 orientation k a.2 ∧
    orientedEFreshBatchEligible SP smallMod BP bigMod
      J ell m cap patterns seen a.2)

/-- Original corrected physical E with its full input Hilbert
orbit average equals the sum over all *explicit indexed*
legal source-oriented E witnesses. Every original E choice that
passes the real global birth test appears exactly once as an INDEX,
even when two choices share the same output Fock multiset.

This is an actual E witness enumeration, not a postulated
abstract state-to-state operator or a distinct-prime-set kernel. -/
theorem physical_oriented_E_indexed_fibre_exact
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) →
      Finset ℕ → ℂ) :
    physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k y seen F =
    ∑ a ∈ physicalOrientedEIndexedLegalFibre
      SP smallMod BP bigMod J ell m cap patterns
      orientation k y seen,
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell)
          cap Vsmall muBig a.1 : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell)
          cap Vsmall muBig y : ℂ)) *
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k a.1 a.2 *
      F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
        J ell m cap patterns a.1 orientation k a.2)
        (seen ∪ (orientedEFreshBirths SP smallMod BP bigMod
          J ell m cap patterns a.2).toFinset) := by
  rw [physicalOrientedMarkedSymmetricE]
  rw [fullPhysicalOrbitAverage_fibre_formula]
  unfold physicalOrientedEIndexedLegalFibre
  simp only [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  by_cases hProj : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x = y
  · simp only [hProj, true_and, ite_true]
    unfold physicalOrientedBirthMarkedE sourceOrientedPhysicalChoices
    simp only [Finset.sum_filter]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hLeg : sourceOrientedPhysicalLegal SP smallMod BP bigMod
        J ell m cap patterns x orientation k z
    · by_cases hBorn : orientedEFreshBatchEligible SP smallMod BP bigMod
          J ell m cap patterns seen z
      · simp only [hLeg, hBorn, and_self, ite_true]
        ring
      · simp [hLeg, hBorn]
    · simp only [hLeg, false_and, ite_false, mul_zero]
  · simp [hProj]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedGIndexedWitnessExpansion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

variable (q rho : ℝ) (N i : ℕ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)

/-- Genuine indexed G source input Fock representative, ordered G
output and individual OLD-zero/new-ghost witness, with the original
global chronological birth eligibility condition. -/
noncomputable def physicalGIndexedEligibleFibre
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    Finset (Σ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      Σ yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) :=
  Finset.univ.filter (fun a =>
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.1 = y ∧
    physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap
      a.1 seen a.2.2)

/-- Actual Hilbert-averaged source G equals the EXHAUSTIVE source
sum over indexed OLD-zero and ghost witnesses. The projected state is
not used to deduplicate G ghost choices or ordered output states.
Global distinct-birth eligibility is the only new indicator. -/
theorem physical_G_indexed_fibre_exact
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) →
      Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
      q rho N i Vsmall Vbig muBig y seen F =
    ∑ a ∈ physicalGIndexedEligibleFibre SP smallMod BP bigMod
      J ell cap y seen,
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
        Vsmall muBig a.1 : ℂ) /
       (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap
         Vsmall muBig y : ℂ)) *
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho N i Vbig muBig a.1 a.2.1 a.2.2 *
      F (physicalFockProjection SP smallMod BP bigMod (J+ell) cap a.2.1)
        (seen ∪ (physicalGhostFreshBirths SP smallMod BP bigMod
          (J+ell) cap a.1 a.2.2).toFinset) := by
  rw [physicalMarkedSymmetricG]
  rw [fullPhysicalOrbitAverage_fibre_formula]
  unfold physicalGIndexedEligibleFibre
  simp only [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Fintype.sum_sigma]
  dsimp only
  by_cases hProj : physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap x = y
  · simp only [hProj, true_and, ite_true]
    unfold physicalGBirthMarkedRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro yg hyg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hBirth : physicalGhostBatchEligible SP smallMod BP bigMod
        (J+ell) cap x seen c
    · simp only [hBirth, and_self, ite_true]
      ring
    · simp [hBirth]
  · simp [hProj]

end Green64FullPhysicalE

end

/-! ## PhysicalFiniteIndexedFubini -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Exact Fubini for a dependent LEGAL pair of original witnesses.
Each index remains a separate source branch, even if two paths have
the same symmetric Fock output. The Sigma carrier counts dependent
E choices and preserves multiplicities without any quotient. -/
theorem finite_nested_legal_sigma
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (G : Finset A) (E : A → Finset B)
    (f : A → B → ℂ) :
    (∑ a ∈ G, ∑ b ∈ E a, f a b) =
    ∑ ab ∈ G.sigma E, f ab.1 ab.2 := by
  rw [Finset.sum_sigma]

/-- The source G scalar, complete E scalar and future test can be
combined on the *actual finite Sigma* witness carrier.
No unproved independence or artificial Markov law is needed. -/
theorem finite_nested_legal_sigma_weighted
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (G : Finset A) (E : A → Finset B)
    (g : A → ℂ) (e : A → B → ℂ) (F : A → B → ℂ) :
    (∑ a ∈ G, g a * (∑ b ∈ E a, e a b * F a b)) =
    ∑ ab ∈ G.sigma E,
      (g ab.1 * e ab.1 ab.2) * F ab.1 ab.2 := by
  calc
    _ = ∑ a ∈ G, ∑ b ∈ E a,
        (g a * e a b) * F a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := finite_nested_legal_sigma G E
      (fun a b => (g a * e a b) * F a b)

end Green64FullPhysicalE

end

