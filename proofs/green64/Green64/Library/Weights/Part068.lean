module

public import Green64.Library.Weights.Part067
public import Green64.Library.Correlation.Part052
public import Green64.Library.Correlation.Part049
public import Green64.Library.Correlation.Part048
public import Green64.Library.Weights.Part018

@[expose] public section

/-!
# Weights / Part068

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualGESpectralDivisorCap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE FINITE upper divisor of all literal physical E source
choices, over EVERY reachable Fock×seen intermediate state at a
FIXED actual orientation. This is not a freely invented bound. -/
noncomputable def sourceOriginalActualGEDivisorCap434 (o k : ℤ) : ℕ :=
  (Finset.univ : Finset H).sup (fun b =>
    (sourceOriginalActualSignedEThetaSupport434
       SP sm BP bm J ell m cap patterns o k b).sup id)
/-- The arithmetic support of a TRUE physical E transition is
bounded by its actual maximum over all reachable physical states. -/
theorem source_original_ACTUAL_GE_divisor_cap434
    (o k : ℤ) (b : H) (D : ℕ)
    (hD : D ∈ sourceOriginalActualSignedEThetaSupport434
      SP sm BP bm J ell m cap patterns o k b) :
    D ≤ sourceOriginalActualGEDivisorCap434
      SP sm BP bm J ell m cap patterns o k := by
  classical
  unfold sourceOriginalActualGEDivisorCap434
  have h1 : D ≤ (sourceOriginalActualSignedEThetaSupport434
      SP sm BP bm J ell m cap patterns o k b).sup id :=
    Finset.le_sup (f := id) hD
  have h2 : (sourceOriginalActualSignedEThetaSupport434
      SP sm BP bm J ell m cap patterns o k b).sup id ≤
      (Finset.univ : Finset H).sup (fun b : H =>
        (sourceOriginalActualSignedEThetaSupport434
          SP sm BP bm J ell m cap patterns o k b).sup id) :=
    Finset.le_sup (s := (Finset.univ : Finset H))
      (f := fun b : H => (sourceOriginalActualSignedEThetaSupport434
        SP sm BP bm J ell m cap patterns o k b).sup id)
      (Finset.mem_univ b)
  exact h1.trans h2

/-- The TRUE finite divisor capacity covering BOTH alternating
physical orientations at all chronological visits. Independent of
joint K, ghost G, OLD projector, and arbitrary physical future. -/
noncomputable def sourceOriginalActualGEDualDivisorCap434 (k : ℤ) : ℕ :=
  max (sourceOriginalActualGEDivisorCap434
    SP sm BP bm J ell m cap patterns 1 k)
    (sourceOriginalActualGEDivisorCap434
      SP sm BP bm J ell m cap patterns (-1) k)

/-- Every original orientation ± has all physical E divisors
under the SAME genuinely finite dual-orientation cap. -/
theorem source_original_ACTUAL_GE_dual_divisor_cap434
    (o k : ℤ) (ho : o=1 ∨ o=-1) (b : H) (D : ℕ)
    (hD : D ∈ sourceOriginalActualSignedEThetaSupport434
      SP sm BP bm J ell m cap patterns o k b) :
    D ≤ sourceOriginalActualGEDualDivisorCap434
      SP sm BP bm J ell m cap patterns k := by
  have hcap := source_original_ACTUAL_GE_divisor_cap434
    SP sm BP bm J ell m cap patterns o k b D hD
  rcases ho with ho | ho
  · subst o
    exact hcap.trans (le_max_left _ _)
  · subst o
    exact hcap.trans (le_max_right _ _)

/-- A single G_i P_T E_i P_T entry cannot create signed Fourier
frequency beyond |k| times its REAL reachable source divisor cap.
The ghost transition has no Fourier phase and all K coefficients
are complex, hence no independent-path assumption enters. -/
theorem source_original_ACTUAL_GE_true_frequency_radius434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (ho : o = 1 ∨ o = -1)
    (N i T : ℕ) (a c : H) (freq : ℤ)
    (hne : (sourceOriginalActualProjectedGEThetaLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k N i T a c).coeff freq ≠ 0) :
    freq.natAbs ≤ k.natAbs *
      sourceOriginalActualGEDualDivisorCap434
        SP sm BP bm J ell m cap patterns k := by
  have hoabs : o.natAbs = 1 := by
    rcases ho with hh|hh <;> simp [hh]
  rw [source_original_ACTUAL_projected_GE_Laurent_coeff434] at hne
  by_contra hgt
  apply hne
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro D hD
  have hle := source_original_ACTUAL_GE_dual_divisor_cap434
    SP sm BP bm J ell m cap patterns o k ho b D hD
  have hfreq : o*k*(D:ℤ) ≠ freq := by
    intro hh
    have hb : freq.natAbs ≤ k.natAbs *
      sourceOriginalActualGEDualDivisorCap434
        SP sm BP bm J ell m cap patterns k := by
      calc
        freq.natAbs = (o*k*(D:ℤ)).natAbs := by rw [hh]
        _ = k.natAbs * D := by
          simp only [Int.natAbs_mul,Int.natAbs_natCast,hoabs,one_mul]
        _ ≤ _ := Nat.mul_le_mul_left _ hle
    exact hgt hb
  simp [hfreq]

/-- Every visit of the TRUE alternating G_i P_T E_i P_T schedule
has the same uniform physical |k|*Dmax spectral radius. This holds
simultaneously for CLEAN and DIRTY predicates and original joint K. -/
theorem source_original_ACTUAL_GE_schedule_frequency_radius434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ)
    (N T i : ℕ) (a b : H) (freq : ℤ)
    (hne : (sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta k N T i a b).coeff freq ≠ 0) :
    freq.natAbs ≤ k.natAbs *
      sourceOriginalActualGEDualDivisorCap434
        SP sm BP bm J ell m cap patterns k := by
  have ho : physicalAlternatingSign i=1 ∨
      physicalAlternatingSign i=-1 := by
    unfold physicalAlternatingSign
    split_ifs <;> simp
  exact source_original_ACTUAL_GE_true_frequency_radius434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
    zeta (physicalAlternatingSign i) k ho N i T a b freq hne
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGEDivisorSupRealBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Nat finite supremum preserves a uniform REAL upper bound,
without an added cardinality factor. -/
theorem source_original_true_nat_sup_real_le434
    {I : Type} [DecidableEq I] (s : Finset I)
    (f : I → ℕ) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ i ∈ s, (f i : ℝ) ≤ U) :
    ((s.sup f : ℕ) : ℝ) ≤ U := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using hU
  | @insert a s ha ih =>
      have haU : (f a : ℝ) ≤ U := h a (Finset.mem_insert_self ..)
      have hsU : ∀ i ∈ s, (f i : ℝ) ≤ U := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      simpa only [Finset.sup_insert, Nat.cast_max, max_le_iff] using
        (And.intro haU (ih hsU))
/-- Any uniform REAL bound on the ACTUAL physical oriented source
D of every Fock state/choice bounds the full signed G_i E_i
divisor support, simultaneously for every seen history and
every reachable intermediate G state. No K norm or future
independence enters this structural comparison. -/
theorem source_original_ACTUAL_GE_divisor_cap_real_le434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (o k : ℤ) (U : ℝ) (hU : 0 ≤ U)
    (hD : ∀ (x : FullPhysicalState SP sm BP bm (J+ell) cap)
      (ch : FullOrientedSourceChoice
        SP sm BP bm J ell m cap patterns x),
      ((sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns ch.1) ch.2.1 x ch.2.2.1.sigmaBig
        ch.2.2.2.1 : ℕ) : ℝ) ≤ U) :
    ((sourceOriginalActualGEDivisorCap434
      SP sm BP bm J ell m cap patterns o k : ℕ) : ℝ) ≤ U := by
  classical
  let H := sourceOriginalActualSignedHistoryState434
    SP sm BP bm J ell cap
  let supp : H → Finset ℕ := fun b =>
    sourceOriginalActualSignedEThetaSupport434
      SP sm BP bm J ell m cap patterns o k b
  have hfreq : ∀ b : H, ∀ D ∈ supp b, (D : ℝ) ≤ U := by
    intro b D hmem
    change D ∈ sourceOriginalActualFrameThetaSupport434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap b.val.1)
      b.val.2 o k at hmem
    obtain ⟨r,hr,hreq⟩ := Finset.mem_image.mp hmem
    rw [←hreq]
    unfold sourceOriginalActualFrameThetaFreq434
    split_ifs with hx
    · exact hD _ _
    · simpa using hU
  unfold sourceOriginalActualGEDivisorCap434
  apply source_original_true_nat_sup_real_le434
    (Finset.univ : Finset H)
    (fun b => (supp b).sup id) U hU
  intro b hb
  exact source_original_true_nat_sup_real_le434
    (supp b) id U hU (hfreq b)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentInitialMaskChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- A signed actual first-DIRTY path amplitude divided by its
initial vacuum weight is the same exact Laurent path coefficient
when that weight is nonzero. When the actual initial weight
vanishes BOTH sides are zero. No epsilon regularization of zero. -/
theorem source_original_ACTUAL_signed_DIRTY_normalized_path_eq434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (w : H → ℂ)
    (n start : ℕ) (a : H) (path : Fin n → H) (freq : ℤ) :
    (if w a = 0 then 0 else
      sourceOriginalSignedLaurentDIRTYPathAmplitude434
        C D f w n start (a,path) freq / w a) =
    (if w a = 0 then 0 else
      (sourceOriginalSignedLaurentDirtyPathWeight434
        C D f n start a path).coeff freq) := by
  by_cases hw : w a = 0
  · simp [hw]
  · simp only [if_neg hw]
    unfold sourceOriginalSignedLaurentDIRTYPathAmplitude434
    field_simp [hw]
/-- After COMPLEX summation over all REAL successive states,
the signed normalized first-DIRTY future is exactly the Fourier
coefficient of ONE finite ACTUAL DIRTY matrix Laurent chain
masked only at states with zero initial physical vacuum weight.
No path-count multiplication or TV norm is introduced. -/
theorem source_original_ACTUAL_signed_DIRTY_normalized_future_chain434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (w : H → ℂ)
    (n start : ℕ) (a : H) (freq : ℤ) :
    (∑ path : Fin n → H,
      if w a = 0 then 0 else
        sourceOriginalSignedLaurentDIRTYPathAmplitude434
          C D f w n start (a,path) freq / w a) =
    (if w a = 0 then 0 else
      (sourceOriginalSignedLaurentDirtyChain434
        C D n start f a).coeff freq) := by
  classical
  by_cases hw : w a = 0
  · simp [hw]
  · simp only [if_neg hw]
    calc
      (∑ path : Fin n → H,
          sourceOriginalSignedLaurentDIRTYPathAmplitude434
            C D f w n start (a,path) freq / w a) =
        ∑ path : Fin n → H,
          (sourceOriginalSignedLaurentDirtyPathWeight434
            C D f n start a path).coeff freq := by
          apply Finset.sum_congr rfl
          intro path hp
          simpa only [if_neg hw] using
            source_original_ACTUAL_signed_DIRTY_normalized_path_eq434
              C D f w n start a path freq
      _ = (sourceOriginalSignedLaurentDirtyChain434
            C D n start f a).coeff freq := by
          rw [source_original_ACTUAL_signed_Laurent_DIRTY_state_path_sum434
            C D f n start a,
            AddMonoidAlgebra.coeff_sum,Finsupp.finset_sum_apply]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentKDivisible -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- For ONE fixed actual chronological state path, the FULL
signed Laurent amplitude is supported on the true kℤ lattice
when each physical transition and terminal coefficient is. -/
theorem source_original_TRUE_Laurent_FULL_path_K434
    {H : Type} [Fintype H] (k : ℤ)
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (F : H → AddMonoidAlgebra ℂ ℤ)
    (hM : ∀ i a b, sourceOriginalLaurentKSupported434 k (M i a b))
    (hF : ∀ a, sourceOriginalLaurentKSupported434 k (F a)) :
    ∀ (n start : ℕ) (a : H) (path : Fin n → H),
      sourceOriginalLaurentKSupported434 k
        (sourceOriginalSignedLaurentPathWeight434 M F n start a path) := by
  intro n
  induction n with
  | zero =>
    intro start a path
    exact hF a
  | succ n ih =>
    intro start a path
    change sourceOriginalLaurentKSupported434 k
      (M start a (path 0) *
        sourceOriginalSignedLaurentPathWeight434
          M F n (start+1) (path 0) (Fin.tail path))
    exact source_original_Laurent_K_mul434 k
      (M start a (path 0))
      (sourceOriginalSignedLaurentPathWeight434
        M F n (start+1) (path 0) (Fin.tail path))
      (hM start a (path 0)) (ih (start+1) (path 0) (Fin.tail path))

/-- The SAME path's CLEAN-prefix / first-DIRTY insertion / full
continuation signed interference remains supported in kℤ,
without replacing chronological histories by iid draws. -/
theorem source_original_TRUE_Laurent_DIRTY_path_K434
    {H : Type} [Fintype H] (k : ℤ)
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (F : H → AddMonoidAlgebra ℂ ℤ)
    (hC : ∀ i a b, sourceOriginalLaurentKSupported434 k (C i a b))
    (hD : ∀ i a b, sourceOriginalLaurentKSupported434 k (D i a b))
    (hF : ∀ a, sourceOriginalLaurentKSupported434 k (F a)) :
    ∀ (n start : ℕ) (a : H) (path : Fin n → H),
      sourceOriginalLaurentKSupported434 k
        (sourceOriginalSignedLaurentDirtyPathWeight434 C D F
          n start a path) := by
  intro n
  induction n with
  | zero =>
    intro start a path
    change sourceOriginalLaurentKSupported434 k 0
    exact source_original_Laurent_K_zero434 k
  | succ n ih =>
    intro start a path
    change sourceOriginalLaurentKSupported434 k
      (D start a (path 0) *
        sourceOriginalSignedLaurentPathWeight434
          (fun i x y => C i x y + D i x y)
          F n (start+1) (path 0) (Fin.tail path) +
      C start a (path 0) *
        sourceOriginalSignedLaurentDirtyPathWeight434
          C D F n (start+1) (path 0) (Fin.tail path))
    apply source_original_Laurent_K_add434
    · exact source_original_Laurent_K_mul434 k _ _
        (hD start a (path 0))
        (source_original_TRUE_Laurent_FULL_path_K434 k
          (fun i x y => C i x y + D i x y) F
          (fun i x y => source_original_Laurent_K_add434 k _ _
            (hC i x y) (hD i x y))
          hF n (start+1) (path 0) (Fin.tail path))
    · exact source_original_Laurent_K_mul434 k _ _
        (hC start a (path 0))
        (ih (start+1) (path 0) (Fin.tail path))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalGEKSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 8500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The literal ORIGINAL G/E matrix entry, at every physical state
and chronological index, has phase o*k*D. Consequently its FULL
signed Fourier support is in kℤ. OLD projectors, joint K, moving
seen, and original alternating orientation remain unchanged. -/
theorem source_original_ACTUAL_PHYSICAL_GE_schedule_k_lattice434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (N T i : ℕ) (a b : H) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalActualProjectedGEScheduleLaurent434
        SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta k N T i a b) := by
  unfold sourceOriginalActualProjectedGEScheduleLaurent434
    sourceOriginalActualProjectedGEThetaLaurent434
  apply source_original_Laurent_K_sum434
  intro z hz
  apply source_original_Laurent_K_sum434
  intro D hD
  apply source_original_Laurent_K_single434
  refine ⟨(physicalAlternatingSign i) * (D:ℤ),?_⟩
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedProjectedChainMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 27000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The original REAL projected G followed by full source E equals
the genuine signed G*PEP one-step physical definition. -/
theorem source_original_ACTUAL_FULL_projected_one_step_physical434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N i T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ) :
    sourceOriginalActualProjectedOneStep434 SP sm BP bm J ell m cap patterns
      q rho N i T Vs V mu K zeta theta k F y seen =
    sourceOriginalActualSignedProjectedGEPhysical434
      SP sm BP bm J ell m cap patterns (fun _ _ => True)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta theta (physicalAlternatingSign i) k N i T F y seen := by
  classical
  unfold sourceOriginalActualProjectedOneStep434
    sourceOriginalActualSignedProjectedGEPhysical434
  congr 1
  funext yg sg
  by_cases hp : (∑ g : BG,(yg.2 g).2.card) ≤ T
  · simp only [if_pos hp]
    exact source_original_ACTUAL_E_frame_true434
      SP sm BP bm J ell m cap patterns
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta theta (physicalAlternatingSign i) k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
      (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T
        then F out st else 0)
  · simp only [if_neg hp]

/-- Original Fock×seen terminal G at the actual final clock index.
This is the same literal ghost G_N used in the source PEP chain. -/
def sourceOriginalActualSignedProjectedTerminalG434
    (q rho : ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (N endIndex : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    H → ℂ :=
  fun a => sourceOriginalPhysicalGhostUnseenPrimeRow434
    SP sm BP bm (J+ell)
    q rho N endIndex V mu a.val.1 a.val.2 F

/-- The ORIGINAL fully projected frame G/E chain equals the scheduled
product of its TRUE signed G_i P_T E_i P_T matrices, including the
final original ghost G, on every reachable Fock×seen starting state.
No extra history maximum is introduced or assumed. -/
theorem source_original_ACTUAL_FULL_projected_chain_matrix_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2 =
    sourceOriginalSignedMatrixChain434
      (sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns (fun _ _ => True)
        q rho Vs V mu K zeta theta k N T)
      n start
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N (start+n) F) a := by
  induction n generalizing start a with
  | zero => rfl
  | succ n ih =>
      let K_i := memoryOrientationK BP J ell m patterns
        K (physicalAlternatingSign start)
      let Tail := sourceOriginalOLDProjectedFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F
      have hStep := source_original_ACTUAL_projected_chain_succ_is_step434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2
      have hTrue := source_original_ACTUAL_FULL_projected_one_step_physical434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N start T
        Tail a.val.1 a.val.2
      have hRow := source_original_ACTUAL_signed_projected_GE_physical_exact434
        SP sm BP bm J ell m cap patterns
        hi hcap (fun _ _ => True) q rho Vs V mu hVs hmu
        K_i zeta theta (physicalAlternatingSign start) k N start T Tail a
      rw [hStep,hTrue,hRow]
      change (∑ b : H,
          sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns (fun _ _ => True)
            q rho Vs V mu K zeta theta k N T start a b *
          Tail b.val.1 b.val.2) =
        ∑ b : H,
          sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns (fun _ _ => True)
            q rho Vs V mu K zeta theta k N T start a b *
          sourceOriginalSignedMatrixChain434
            (sourceOriginalActualSignedProjectedGESchedule434
              SP sm BP bm J ell m cap patterns (fun _ _ => True)
              q rho Vs V mu K zeta theta k N T)
            n (start+1)
            (sourceOriginalActualSignedProjectedTerminalG434
              SP sm BP bm J ell cap q rho V mu N (start+(n+1)) F) b
      apply Finset.sum_congr rfl
      intro b hb
      have hIndex : (start+1)+n = start+(n+1) := by omega
      have hbTail := ih (start+1) b
      rw [hIndex] at hbTail
      dsimp only [Tail]
      rw [hbTail]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedCleanChainMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 27000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The literal CLEAN G/E visit equals the genuine signed
G followed by the exact two-sided OLD-projected CLEAN E frame. -/
theorem source_original_ACTUAL_CLEAN_projected_one_step_physical434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalOLDProjectedCleanFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (n+1) start F y seen =
    sourceOriginalActualSignedProjectedGEPhysical434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
      zeta theta (physicalAlternatingSign start) k N start T
      (sourceOriginalOLDProjectedCleanFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F) y seen := by
  rfl

/-- The ENTIRE true chronological CLEAN G/E frame chain is represented
by the original exact complex Fock×seen CLEAN schedule, with terminal G.
No independent E/G history or positive majorant. -/
theorem source_original_ACTUAL_CLEAN_projected_chain_matrix_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalOLDProjectedCleanFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2 =
    sourceOriginalSignedMatrixChain434
      (sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta k N T)
      n start
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N (start+n) F) a := by
  induction n generalizing start a with
  | zero => rfl
  | succ n ih =>
      let K_i := memoryOrientationK BP J ell m patterns
        K (physicalAlternatingSign start)
      let Tail := sourceOriginalOLDProjectedCleanFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F
      have hStep := source_original_ACTUAL_CLEAN_projected_one_step_physical434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta
        k N T n start F a.val.1 a.val.2
      have hRow := source_original_ACTUAL_signed_projected_GE_physical_exact434
        SP sm BP bm J ell m cap patterns
        hi hcap (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu hVs hmu K_i zeta theta
        (physicalAlternatingSign start) k N start T Tail a
      rw [hStep,hRow]
      change (∑ b : H,
          sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V mu K zeta theta k N T start a b *
          Tail b.val.1 b.val.2) =
        ∑ b : H,
          sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V mu K zeta theta k N T start a b *
          sourceOriginalSignedMatrixChain434
            (sourceOriginalActualSignedProjectedGESchedule434
              SP sm BP bm J ell m cap patterns (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
              q rho Vs V mu K zeta theta k N T)
            n (start+1)
            (sourceOriginalActualSignedProjectedTerminalG434
              SP sm BP bm J ell cap q rho V mu N (start+(n+1)) F) b
      apply Finset.sum_congr rfl
      intro b hb
      have hIndex : (start+1)+n = start+(n+1) := by omega
      have hbTail := ih (start+1) b
      rw [hIndex] at hbTail
      dsimp only [Tail]
      rw [hbTail]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYChainMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The ORIGINAL signed chronological first-DIRTY physical frame
recursion equals an exact complex CLEAN-prefix/DIRTY-insertion/FULL-suffix
finite matrix expression on the SAME reachable Fock×seen state. -/
theorem source_original_ACTUAL_DIRTY_insertion_chain_matrix_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
      SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2 =
    let Clean := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k N T
    let Dirty := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k N T
    sourceOriginalSignedMatrixDirtyChain434 Clean Dirty n start
      (sourceOriginalActualSignedProjectedTerminalG434 SP sm BP bm
        J ell cap q rho V mu N (start+n) F) a := by
  let Full := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns (fun _ _ => True)
    q rho Vs V mu K zeta theta k N T
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu N (start+n) F
  have hTele := source_original_MEMORY_PEP_PCLEAN_frame_telescoping434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T F n start a.val.1 a.val.2
  have hFull := source_original_ACTUAL_FULL_projected_chain_matrix_exact434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V mu hVs hmu K zeta theta k N T n start F a
  have hClean := source_original_ACTUAL_CLEAN_projected_chain_matrix_exact434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V mu hVs hmu K zeta theta k N T n start F a
  have hDuhamel := source_original_ACTUAL_signed_projected_GE_Duhamel434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T n start f a
  -- The same physical G/E chain and exact terminal G appear in
  -- both matrix identities. The difference is precisely the first insertion.
  calc
    _ = sourceOriginalOLDProjectedFrameGEChain434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2 -
        sourceOriginalOLDProjectedCleanFrameGEChain434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n start F a.val.1 a.val.2 :=
            hTele.symm
    _ = sourceOriginalSignedMatrixChain434 Full n start f a -
        sourceOriginalSignedMatrixChain434 Clean n start f a := by
          rw [hFull,hClean]
    _ = _ := hDuhamel
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPrefixTranspose -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact signed transport of a prefix row through a finite complex
kernel. No adjoint conjugation: this is the genuine bilinear
transpose corresponding to the original complex Fock weights. -/
def sourceOriginalSignedPrefixTranspose434 {H : Type} [Fintype H]
    (M : H → H → ℂ) (w : H → ℂ) (b : H) : ℂ :=
  ∑ a : H, w a * M a b

/-- Original chronological CLEAN prefix, propagated FORWARD by
the real complex transpose on one joint Fock×seen carrier. -/
def sourceOriginalSignedForwardPrefix434 {H : Type} [Fintype H]
    (C : ℕ → H → H → ℂ) :
    (n start : ℕ) → (H → ℂ) → H → ℂ
  | 0,_,w => w
  | n+1,start,w =>
      sourceOriginalSignedForwardPrefix434 C n (start+1)
        (sourceOriginalSignedPrefixTranspose434 (C start) w)

/-- Exact bilinear prefix/suffix identity for arbitrarily many
chronological signed CLEAN visits, on the SAME finite joint
Fock×cumulative-seen state at every intermediate index. -/
theorem source_original_signed_forward_prefix_pairing434
    {H : Type} [Fintype H] (C : ℕ → H → H → ℂ)
    (n start : ℕ) (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalSignedMatrixChain434 C n start f a) =
    ∑ b : H, sourceOriginalSignedForwardPrefix434 C n start w b * f b := by
  classical
  induction n generalizing start w with
  | zero =>
      rfl
  | succ n ih =>
      let T := sourceOriginalSignedMatrixChain434 C n (start+1) f
      let M := C start
      let w' := sourceOriginalSignedPrefixTranspose434 M w
      change (∑ a : H, w a * (∑ b : H, M a b * T b)) =
        ∑ b : H,
          sourceOriginalSignedForwardPrefix434 C n (start+1) w' b * f b
      calc
        _ = ∑ a : H, ∑ b : H, (w a * M a b) * T b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = ∑ b : H, ∑ a : H, (w a * M a b) * T b := by
          rw [Finset.sum_comm]
        _ = ∑ b : H, w' b * T b := by
          apply Finset.sum_congr rfl
          intro b hb
          change (∑ a : H, (w a * M a b) * T b) =
            (∑ a : H, w a * M a b) * T b
          rw [Finset.sum_mul]
        _ = _ := ih (start+1) w'
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedGEAlgebraPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact finite complex-bilinear pairing which transports ONLY
the G factor to a signed prefix and leaves the original E matrix
on the suffix. No positivity, no new history state, no kernel
symmetrization and no conjugation. -/
theorem source_original_SIGNED_G_E_postghost_pairing434
    {H : Type} [Fintype H]
    (G E : H → H → ℂ) (w f : H → ℂ) :
    (∑ a : H, w a * (∑ c : H,
      sourceOriginalSignedMatrixProduct434 G E a c * f c)) =
    ∑ b : H, sourceOriginalSignedPrefixTranspose434 G w b *
      (∑ c : H, E b c * f c) := by
  classical
  calc
    _ = ∑ a : H, w a * (∑ b : H,
          G a b * (∑ c : H, E b c * f c)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_original_signed_matrix_product_apply434]
    _ = ∑ a : H, ∑ b : H,
          (w a * G a b) * (∑ c : H, E b c * f c) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ b : H, ∑ a : H,
          (w a * G a b) * (∑ c : H, E b c * f c) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      change (∑ a : H, (w a * G a b) *
        (∑ c : H, E b c * f c)) =
        (∑ a : H, w a * G a b) * (∑ c : H, E b c * f c)
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInsertionPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact signed insertion term: the ORIGINAL chronological CLEAN
prefix of length j, then ONE DIRTY matrix, then a FULL suffix of
length r, on the SAME joint Fock×seen state. -/
def sourceOriginalSignedMatrixAt434 {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (j r start : ℕ)
    (f : H → ℂ) : H → ℂ :=
  sourceOriginalSignedMatrixChain434 C j start
    (sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        r (start+j+1) f))

/-- Actual COMPLEX bilinear prefix/suffix pairing for ONE signed
insertion. The prefix is propagated by the exact matrix transpose;
nothing is conjugated, resampled or made positive. -/
theorem source_original_signed_insertion_prefix_suffix_pairing434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (j r start : ℕ)
    (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalSignedMatrixAt434 C D j r start f a) =
    ∑ b : H,
      sourceOriginalSignedForwardPrefix434 C j start w b *
      sourceOriginalSignedMatrixAction434 (D (start+j))
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D)
          r (start+j+1) f) b := by
  exact source_original_signed_forward_prefix_pairing434
    C j start w
    (sourceOriginalSignedMatrixAction434 (D (start+j))
      (sourceOriginalSignedMatrixChain434
        (sourceOriginalSignedKernelAdd434 C D)
        r (start+j+1) f))

/-- Prepending one actual CLEAN visit to the first-insertion
observable adds one unit of chronology, without resetting history. -/
theorem source_original_signed_matrix_at_cons434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (j r start : ℕ)
    (f : H → ℂ) (a : H) :
    sourceOriginalSignedMatrixAt434 C D (j+1) r start f a =
    sourceOriginalSignedMatrixAction434 (C start)
      (sourceOriginalSignedMatrixAt434 C D j r (start+1) f) a := by
  have hi : start+(j+1) = (start+1)+j := by omega
  have hj : start+(j+1)+1 = (start+1)+j+1 := by omega
  simp only [sourceOriginalSignedMatrixAt434,
    sourceOriginalSignedMatrixChain434,hi,hj]

/-- The original signed complex matrix action commutes with
finite sums over insertion positions, without any triangle bound. -/
theorem source_original_signed_matrix_action_sum434
    {H I : Type} [Fintype H]
    (M : H → H → ℂ) (s : Finset I) (g : I → H → ℂ) (a : H) :
    sourceOriginalSignedMatrixAction434 M
      (fun b => ∑ j ∈ s, g j b) a =
    ∑ j ∈ s, sourceOriginalSignedMatrixAction434 M (g j) a := by
  classical
  unfold sourceOriginalSignedMatrixAction434
  calc
    _ = ∑ b : H, ∑ j ∈ s, M a b * g j b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ = ∑ j ∈ s, ∑ b : H, M a b * g j b := by
      rw [Finset.sum_comm]
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDuhamelPositions -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- For ANY finite signed complex chronological G/E kernels, the
first-DIRTY Duhamel recursion is EXACTLY the signed sum over
chronological insertion positions, with CLEAN on the left and FULL
on the right. The same finite Fock×seen state is carried throughout. -/
theorem source_original_signed_matrix_dirty_positions434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ)
    (n start : ℕ) (f : H → ℂ) (a : H) :
    sourceOriginalSignedMatrixDirtyChain434 C D n start f a =
    ∑ j ∈ Finset.range n,
      sourceOriginalSignedMatrixAt434 C D j (n-(j+1)) start f a := by
  classical
  induction n generalizing start a with
  | zero =>
      simp only [sourceOriginalSignedMatrixDirtyChain434,
        Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
      let Full := sourceOriginalSignedKernelAdd434 C D
      let Tail := sourceOriginalSignedMatrixChain434 Full n (start+1) f
      let Rem := sourceOriginalSignedMatrixDirtyChain434 C D n (start+1) f
      have h0 :
          sourceOriginalSignedMatrixAt434 C D 0 ((n+1)-(0+1)) start f a =
          sourceOriginalSignedMatrixAction434 (D start) Tail a := by
        simp only [sourceOriginalSignedMatrixAt434,
          sourceOriginalSignedMatrixChain434,Nat.zero_add,
          Nat.add_sub_cancel_left]
        rfl
      have htail :
          (∑ j ∈ Finset.range n,
            sourceOriginalSignedMatrixAt434
              C D (j+1) ((n+1)-((j+1)+1)) start f a) =
          sourceOriginalSignedMatrixAction434 (C start) Rem a := by
        calc
          _ = ∑ j ∈ Finset.range n,
                sourceOriginalSignedMatrixAction434 (C start)
                  (sourceOriginalSignedMatrixAt434
                    C D j (n-(j+1)) (start+1) f) a := by
              apply Finset.sum_congr rfl
              intro j hj
              have hj : (n+1)-((j+1)+1) = n-(j+1) := by omega
              rw [hj,source_original_signed_matrix_at_cons434]
          _ = sourceOriginalSignedMatrixAction434 (C start)
                (fun b => ∑ j ∈ Finset.range n,
                  sourceOriginalSignedMatrixAt434
                    C D j (n-(j+1)) (start+1) f b) a := by
              exact (source_original_signed_matrix_action_sum434
                (C start) (Finset.range n)
                (fun j b => sourceOriginalSignedMatrixAt434
                  C D j (n-(j+1)) (start+1) f b) a).symm
          _ = sourceOriginalSignedMatrixAction434 (C start) Rem a := by
              congr 1
              funext b
              exact (ih (start+1) b).symm
      change sourceOriginalSignedMatrixAction434 (D start) Tail a +
          sourceOriginalSignedMatrixAction434 (C start) Rem a =
        ∑ j ∈ Finset.range (n+1),
          sourceOriginalSignedMatrixAt434 C D j ((n+1)-(j+1)) start f a
      rw [Finset.sum_range_succ']
      rw [h0,htail]
      exact add_comm _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDirtyPrefixSuffix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact signed complex-bilinear Duhamel pairing on ANY finite
joint physical-state/history carrier. At visit j the true CLEAN
prefix acts by its transpose, the exact DIRTY row is inserted once,
and the genuine FULL signed suffix follows it.
No absolutes, no independent history, and no norm assumptions. -/
theorem source_original_signed_dirty_prefix_suffix_sum434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ)
    (n start : ℕ) (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalSignedMatrixDirtyChain434
      C D n start f a) =
    ∑ j ∈ Finset.range n, ∑ b : H,
      sourceOriginalSignedForwardPrefix434 C j start w b *
      sourceOriginalSignedMatrixAction434 (D (start+j))
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D)
          (n-(j+1)) (start+j+1) f) b := by
  classical
  calc
    _ = ∑ a : H, w a * (∑ j ∈ Finset.range n,
        sourceOriginalSignedMatrixAt434 C D j (n-(j+1)) start f a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_original_signed_matrix_dirty_positions434 C D n start f a]
    _ = ∑ a : H, ∑ j ∈ Finset.range n,
        w a * sourceOriginalSignedMatrixAt434 C D j (n-(j+1)) start f a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n, ∑ a : H,
        w a * sourceOriginalSignedMatrixAt434
          C D j (n-(j+1)) start f a := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact source_original_signed_insertion_prefix_suffix_pairing434
        C D j (n-(j+1)) start w f
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalDirtyPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The TRUE first-DIRTY frame-chain signed pairing with an arbitrary
initial complex Fock×seen measure is EXACTLY a chronological sum:
CLEAN-prefix transpose, ONE exact projected DIRTY G/E matrix,
and the FULL projected signed suffix, with the same joint history.
This is a theorem on the actual physical recursion, not a surrogate. -/
theorem source_original_ACTUAL_PHYSICAL_first_DIRTY_prefix_suffix434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (N T n start : ℕ)
    (w : H → ℂ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    let Clean := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k N T
    let Dirty := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k N T
    let f := sourceOriginalActualSignedProjectedTerminalG434
      SP sm BP bm J ell cap q rho V mu N (start+n) F
    (∑ a : H, w a *
      sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start F
        a.val.1 a.val.2) =
    ∑ j ∈ Finset.range n, ∑ b : H,
      sourceOriginalSignedForwardPrefix434 Clean j start w b *
      sourceOriginalSignedMatrixAction434 (Dirty (start+j))
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 Clean Dirty)
          (n-(j+1)) (start+j+1) f) b := by
  dsimp only
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu N (start+n) F
  have hAt (a : H) := source_original_ACTUAL_DIRTY_insertion_chain_matrix_exact434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V mu hVs hmu K zeta theta k N T n start F a
  calc
    _ = ∑ a : H, w a *
      sourceOriginalSignedMatrixDirtyChain434 Clean Dirty n start f a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hAt a]
    _ = _ := source_original_signed_dirty_prefix_suffix_sum434
      Clean Dirty n start w f
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialFockWeight -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The REAL original initial vacuum/Fock sector with nonzero vacuum
and no repeated initial numerical births. Terms outside are exactly
zero in the authentic source physical root. -/
def sourceOriginalActualSignedInitialGood434 :
    Finset (FullPhysicalOutput SP sm BP bm (J+ell)) :=
  (physicalFockOrbitSupport SP sm BP bm (J+ell) cap).filter
    (fun y => physicalVacuum SP sm BP bm J ell y ≠ 0 ∧
      (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup)

noncomputable instance :
    Fintype ({y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap}) :=
  Finset.fintypeCoeSort
    (sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap)

/-- Embed each genuine nonvanishing initial vacuum/Fock representative
into the finite joint Fock×cumulative-seen carrier. -/
def sourceOriginalActualSignedInitialState434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap}) : H := by
  have hs := (Finset.mem_filter.mp y.property).2
  have hv := hs.1
  have hn := hs.2
  have hr := source_original_MEMORY_initial_reachable434
    SP sm BP bm J ell y.val hv hn
  have hb := source_original_ACTUAL_initial_seen_in_history_pool434
    SP sm BP bm J ell y.val
  exact ⟨⟨y.val,(physicalOutputInitialBirths SP sm BP bm J ell y.val).toFinset⟩,
    source_original_ACTUAL_signed_history_contains_reachable434
      SP sm BP bm J ell cap hcap y.val
      (physicalOutputInitialBirths SP sm BP bm J ell y.val).toFinset hr hb⟩

/-- Complex original Fock/vacuum initial density, seen carried in the
state index, built as a finite sum of genuine vacuum deltas.
No positive reweighting or normalization is introduced. -/
def sourceOriginalActualSignedInitialWeight434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (a : H) : ℂ :=
  ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
    if a = sourceOriginalActualSignedInitialState434 SP sm BP bm J ell cap hcap y
    then (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y.val)
    else 0

/-- Exact complex-bilinear disintegration of the REAL original initial
Fock/vacuum density into finite joint Fock×seen states. The same true
initial seen set travels with each delta. No sum over all histories. -/
theorem source_original_ACTUAL_initial_weight_pairing434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : H → ℂ) :
    (∑ a : H, sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu a * f a) =
    ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
      ((physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y.val)) *
        f (sourceOriginalActualSignedInitialState434
          SP sm BP bm J ell cap hcap y) := by
  classical
  unfold sourceOriginalActualSignedInitialWeight434
  calc
    _ = ∑ a : H,
        ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
          y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
        (if a = sourceOriginalActualSignedInitialState434
          SP sm BP bm J ell cap hcap y then
          (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
            star (physicalVacuum SP sm BP bm J ell y.val) else 0) * f a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_mul]
    _ = ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
          y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
        ∑ a : H,
          (if a = sourceOriginalActualSignedInitialState434
            SP sm BP bm J ell cap hcap y then
            (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
              star (physicalVacuum SP sm BP bm J ell y.val) else 0) * f a := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro y hy
          simp only [ite_mul,zero_mul]
          simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The original physical root contains precisely the nonvanishing,
Nodup initial vacuum orbits. Removing zero terms does not
alter the original signed mass or the history passed to the suffix. -/
theorem source_original_ACTUAL_initial_vacuum_good_sum434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        F y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
       else 0)) =
    ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
        y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
      ((physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y.val)) *
        F y.val (physicalOutputInitialBirths SP sm BP bm J ell y.val).toFinset := by
  classical
  let Supp := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let Good := sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap
  let W : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ :=
    fun y => (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y)
  let phi : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ :=
    fun y => F y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
  change (∑ y ∈ Supp,
      W y * (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        then phi y else 0)) =
    ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) // y ∈ Good},
      W y.val * phi y.val
  calc
    _ = ∑ y ∈ Supp,
        (if (physicalVacuum SP sm BP bm J ell y ≠ 0 ∧
          (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup)
        then W y * phi y else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hv : physicalVacuum SP sm BP bm J ell y = 0
      · simp [hv,W]
      · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        · simp [hv,hn]
        · simp [hv,hn]
    _ = ∑ y ∈ Good, W y * phi y := by
      change (∑ y ∈ Supp,
        if (physicalVacuum SP sm BP bm J ell y ≠ 0 ∧
          (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup)
        then W y * phi y else 0) =
        ∑ y ∈ Supp.filter (fun y =>
          physicalVacuum SP sm BP bm J ell y ≠ 0 ∧
            (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup),
          W y * phi y
      rw [Finset.sum_filter]
    _ = _ := by
      exact (Finset.sum_attach Good (fun y => W y * phi y)).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalRootMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 27000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE physical first-DIRTY signed Memory Fock/vacuum root is
EXACTLY the signed finite Fock×seen matrix Duhamel bilinear pairing,
with the ORIGINAL source initial complex orbit mass and baseline.
No history maximum, independent resampling, or assumed energy bound. -/
theorem source_original_ACTUAL_SIGNED_DIRTY_physical_root_matrix_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    let mu := physicalSourceMuTilde BP bm q (2*R) V
    let Clean := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k (2*R) T
    let Dirty := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k (2*R) T
    let f := sourceOriginalActualSignedProjectedTerminalG434
      SP sm BP bm J ell cap q rho V mu (2*R) (2*R)
      (fun out _ => physicalVacuum SP sm BP bm J ell out)
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      ∑ a : H, sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu a *
        sourceOriginalSignedMatrixDirtyChain434 Clean Dirty (2*R) 0 f a := by
  classical
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  let Vac : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out _ => physicalVacuum SP sm BP bm J ell out
  let Tail := sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T N 0 Vac
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu N N Vac
  let Init := sourceOriginalActualSignedInitialState434
    SP sm BP bm J ell cap hcap
  have hEq :
      sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T =
      sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T := by
    have ht := source_original_MEMORY_PEP_PCLEAN_root_telescoping_of_mass434
      SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K
      zeta theta k R T hVs hmu
    have hp := source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
      SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K
      zeta theta k R T hVs hmu
    exact (ht.symm.trans hp).symm
  have hGood := source_original_ACTUAL_initial_vacuum_good_sum434
    SP sm BP bm J ell cap Vs mu Tail
  have hAt (y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap}) :
      Tail y.val
        (physicalOutputInitialBirths SP sm BP bm J ell y.val).toFinset =
      sourceOriginalSignedMatrixDirtyChain434 Clean Dirty N 0 f (Init y) := by
    have ht := source_original_ACTUAL_DIRTY_insertion_chain_matrix_exact434
      SP sm BP bm J ell m cap patterns hi hcap
      q rho Vs V mu hVs hmu K zeta theta k N T N 0 Vac (Init y)
    simpa only [Nat.zero_add,Tail,Clean,Dirty,f,Init,
      sourceOriginalActualSignedInitialState434] using ht
  have hInit := source_original_ACTUAL_initial_weight_pairing434
    SP sm BP bm J ell cap hcap Vs mu
    (sourceOriginalSignedMatrixDirtyChain434 Clean Dirty N 0 f)
  rw [hEq]
  change Base * (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        Tail y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
       else 0)) =
    Base * (∑ a : H, sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu a *
      sourceOriginalSignedMatrixDirtyChain434 Clean Dirty N 0 f a)
  apply congrArg (fun z : ℂ => Base*z)
  calc
    _ = ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
      ((physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y.val)) *
        Tail y.val (physicalOutputInitialBirths SP sm BP bm J ell y.val).toFinset :=
          hGood
    _ = ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
      ((physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y.val)) *
        sourceOriginalSignedMatrixDirtyChain434 Clean Dirty N 0 f (Init y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hAt y]
    _ = _ := hInit.symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDirtyLaurentChronology -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exactly the source CLEAN-before-DIRTY, FULL-after first-DIRTY
physical G/E chain, with one shared theta Laurent variable and
true accumulated Fock×seen state at every intermediate visit. -/
theorem source_original_ACTUAL_physical_DIRTY_Laurent_chain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N T n start : ℕ)
    (f : H → AddMonoidAlgebra ℂ ℤ) (a : H) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalSignedLaurentDirtyChain434
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP sm BP bm J ell m cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          q rho Vs V mu K zeta k N T)
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP sm BP bm J ell m cap patterns
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP sm BP bm J ell m cap patterns x z)
          q rho Vs V mu K zeta k N T)
        n start f a) =
    sourceOriginalSignedMatrixDirtyChain434
      (sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta k N T)
      (sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs V mu K zeta theta k N T)
      n start (fun b => sourceOriginalActualThetaEval434 theta (f b)) a := by
  rw [source_original_signed_Laurent_DIRTY_chain_eval434]
  congr 1
  · funext i x y
    exact source_original_ACTUAL_projected_GE_schedule_Laurent434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k N T i x y
  · funext i x y
    exact source_original_ACTUAL_projected_GE_schedule_Laurent434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k N T i x y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDirtyLaurentRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

theorem source_original_ACTUAL_theta_eval_constant434
    (theta : ℝ) (z : ℂ) :
    sourceOriginalActualThetaEval434 theta
      (AddMonoidAlgebra.single (0:ℤ) z) = z := by
  rw [source_original_ACTUAL_theta_eval_single434]
  simp [sourceOriginalActualThetaFrequency434]

/-- One exact physical, chronological, Fock/vacuum, OLD-masked
first-DIRTY source root as a finite common-theta Laurent polynomial.
The total signed return frequency accumulates through the original
CLEAN prefix, DIRTY insertion and FULL suffix in the SAME seen state. -/
def sourceOriginalActualPhysicalDIRTYLaurentRoot434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) : AddMonoidAlgebra ℂ ℤ := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta k N T
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N N
        (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
  exact AddMonoidAlgebra.single (0:ℤ)
    (physicalSourceBaselineProduct BP bm q N:ℂ) *
    (∑ a : H, AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu a) *
      sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a)

/-- True first-DIRTY signed physical root at EVERY common real theta
is EXACT evaluation of the same original Laurent polynomial.
No hGain/hEnergy, source03 assumptions or invented cancellation. -/
theorem source_original_ACTUAL_physical_DIRTY_root_Laurent434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g, 0 < Vs g)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualPhysicalDIRTYLaurentRoot434
        SP sm BP bm J ell m cap patterns hcap
        q rho Vs V K zeta k R T) =
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta k N T
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let F : H → AddMonoidAlgebra ℂ ℤ :=
    fun a => AddMonoidAlgebra.single (0:ℤ) (f a)
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  have hCalc :
      sourceOriginalActualThetaEval434 theta
        (sourceOriginalActualPhysicalDIRTYLaurentRoot434
          SP sm BP bm J ell m cap patterns hcap q rho Vs V K zeta k R T) =
      Base * (∑ a : H, w a *
        sourceOriginalSignedMatrixDirtyChain434
          (sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns
            (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V mu K zeta theta k N T)
          (sourceOriginalActualSignedProjectedGESchedule434
            SP sm BP bm J ell m cap patterns
            (fun x z => ¬ sourceOriginalCleanChoice434
              SP sm BP bm J ell m cap patterns x z)
            q rho Vs V mu K zeta theta k N T)
          N 0 f a) := by
    change sourceOriginalActualThetaEval434 theta
      (AddMonoidAlgebra.single (0:ℤ) Base *
        ∑ a : H, (AddMonoidAlgebra.single (0:ℤ) (w a)) *
          sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a) = _
    rw [map_mul, source_original_ACTUAL_theta_eval_constant434, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_mul, source_original_ACTUAL_theta_eval_constant434]
    rw [source_original_ACTUAL_physical_DIRTY_Laurent_chain434]
    simp only [F,source_original_ACTUAL_theta_eval_constant434]
  have hRoot := source_original_ACTUAL_SIGNED_DIRTY_physical_root_matrix_exact434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V K zeta theta k R T hVs hmu
  exact hCalc.trans (by simpa only [N,mu,Base,w,f] using hRoot.symm)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDIRTYFrequencyLattice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 21000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE physical first-DIRTY root has no Fourier coefficient away
from multiples of original k. This is proved through the literal
chronological signed Fock×seen CLEAN-DIRTY-FULL chain, not a made-up
frequency model. It does not assert a log saving on any coefficient. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_k_lattice434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalLaurentKSupported434 k
      (sourceOriginalActualPhysicalDIRTYLaurentRoot434
        SP sm BP bm J ell m cap patterns hcap
        q rho Vs V K zeta k R T) := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta k N T
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N N
        (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  have hC (i : ℕ) (a b : H) :
      sourceOriginalLaurentKSupported434 k (C i a b) := by
    intro d hd
    exact source_original_ACTUAL_projected_GE_off_k_lattice_zero434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta (physicalAlternatingSign i) k N i T a b d hd
  have hD (i : ℕ) (a b : H) :
      sourceOriginalLaurentKSupported434 k (D i a b) := by
    intro d hd
    exact source_original_ACTUAL_projected_GE_off_k_lattice_zero434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta (physicalAlternatingSign i) k N i T a b d hd
  have hF (a : H) :
      sourceOriginalLaurentKSupported434 k (F a) :=
    source_original_Laurent_K_single434 k 0 _ (dvd_zero k)
  have hChain (a : H) :
      sourceOriginalLaurentKSupported434 k
        (sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a) :=
    source_original_Laurent_K_DIRTY_chain434 k C D F hC hD hF N 0 a
  change sourceOriginalLaurentKSupported434 k
    (AddMonoidAlgebra.single (0:ℤ) Base *
      ∑ a : H, AddMonoidAlgebra.single (0:ℤ) (w a) *
        sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a)
  apply source_original_Laurent_K_mul434
  · exact source_original_Laurent_K_single434 k 0 Base (dvd_zero k)
  · apply source_original_Laurent_K_sum434
    intro a ha
    exact source_original_Laurent_K_mul434 k _ _
      (source_original_Laurent_K_single434 k 0 (w a) (dvd_zero k))
      (hChain a)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDIRTYPathGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The TRUE physical DIRTY source root with complete BIG baseline,
vacuum and Fock masses is the exact actual-state path ensemble.
The first-DIRTY insertion remains a signed sum WITHIN EACH path. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_state_path_polynomial434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) :
    let N := 2*R
    let mu := physicalSourceMuTilde BP bm q N V
    let C := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta k N T
    let D := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm
        J ell m cap patterns x z)
      q rho Vs V mu K zeta k N T
    let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
      AddMonoidAlgebra.single (0:ℤ)
        (sourceOriginalActualSignedProjectedTerminalG434
          SP sm BP bm J ell cap q rho V mu N N
          (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
    let w := sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu
    sourceOriginalActualPhysicalDIRTYLaurentRoot434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs V K zeta k R T =
    AddMonoidAlgebra.single (0:ℤ)
      (physicalSourceBaselineProduct BP bm q N : ℂ) *
      sourceOriginalSignedLaurentDIRTYPathEnsemble434 C D F w N 0 := by
  rfl

/-- Root frequency coefficient as one coherent sum over TRUE paths.
No positive TV max, dropped small/big prime, artificial new state,
or assumed cancellation. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_path_frequency434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) :
    let N := 2*R
    let mu := physicalSourceMuTilde BP bm q N V
    let C := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta k N T
    let D := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434 SP sm BP bm
        J ell m cap patterns x z)
      q rho Vs V mu K zeta k N T
    let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
      AddMonoidAlgebra.single (0:ℤ)
        (sourceOriginalActualSignedProjectedTerminalG434
          SP sm BP bm J ell cap q rho V mu N N
          (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
    let w := sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu
    (sourceOriginalActualPhysicalDIRTYLaurentRoot434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs V K zeta k R T).coeff d =
    (physicalSourceBaselineProduct BP bm q N : ℂ) *
      ∑ p : H × (Fin N → H),
        sourceOriginalSignedLaurentDIRTYPathAmplitude434
          C D F w N 0 p d := by
  dsimp only
  rw [source_original_ACTUAL_PHYSICAL_DIRTY_state_path_polynomial434]
  rw [source_original_Laurent_single_future_coeff434,sub_zero]
  rw [source_original_ACTUAL_Laurent_DIRTY_path_coeff434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDIRTYPathCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- TRUE physical DIRTY root Fourier coefficient is a coherent
cross-path Gram on the ORIGINAL chronological Fock×seen state.
The full BIG baseline, Fock initial weights, both OLD endpoint
projectors, alternate E/E*, actual joint K and first-DIRTY insertion
remain present. The pair terms are complex, NOT separately
nonnegative. This is a pointwise exact identity at frequency d. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_path_frequency_gram434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) (freq : ℤ) :
    let N := 2*R
    let mu := physicalSourceMuTilde BP bm q N V
    let C := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta k N T
    let D := sourceOriginalActualProjectedGEScheduleLaurent434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta k N T
    let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
      AddMonoidAlgebra.single (0:ℤ)
        (sourceOriginalActualSignedProjectedTerminalG434
          SP sm BP bm J ell cap q rho V mu N N
          (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
    let w := sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu
    let Base : ℂ := physicalSourceBaselineProduct BP bm q N
    (((‖(sourceOriginalActualPhysicalDIRTYLaurentRoot434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs V K zeta k R T).coeff freq‖^2 : ℝ)) : ℂ) =
    (((‖Base‖^2 : ℝ)) : ℂ) *
      ∑ p : H × (Fin N → H),
        ∑ q : H × (Fin N → H),
          star (sourceOriginalSignedLaurentDIRTYPathAmplitude434
            C D F w N 0 p freq) *
          sourceOriginalSignedLaurentDIRTYPathAmplitude434
            C D F w N 0 q freq := by
  dsimp only
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta k N T
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N N
        (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  let E := sourceOriginalSignedLaurentDIRTYPathEnsemble434 C D F w N 0
  have hCoeff :
      (sourceOriginalActualPhysicalDIRTYLaurentRoot434
        SP sm BP bm J ell m cap patterns hcap
        q rho Vs V K zeta k R T).coeff freq = Base * E.coeff freq := by
    rw [source_original_ACTUAL_PHYSICAL_DIRTY_state_path_polynomial434]
    rw [source_original_Laurent_single_future_coeff434,sub_zero]
  have hGram := source_original_ACTUAL_Laurent_DIRTY_path_gram_at_frequency434
    C D F w N 0 freq
  calc
    (((‖(sourceOriginalActualPhysicalDIRTYLaurentRoot434
        SP sm BP bm J ell m cap patterns hcap
        q rho Vs V K zeta k R T).coeff freq‖^2 : ℝ)) : ℂ) =
        (((‖Base‖^2 : ℝ)) : ℂ) *
          (((‖E.coeff freq‖^2 : ℝ)) : ℂ) := by
            rw [hCoeff,norm_mul,mul_pow]
            push_cast
            ring
    _ = _ := by
      rw [hGram]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDirtyArithmeticCoefficient -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact TOTAL-frequency coefficient of the TRUE Fock/vacuum
first-DIRTY root. All initial physical orbit masses and BIG baseline
stay OUTSIDE the coherent sum over authentic Fock×seen histories.
The chronology inside is CLEAN-before-first-DIRTY, FULL afterwards.
This is an equality of signed complex numbers, not a saving. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_Laurent_coeff434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ) (d : ℤ) :
    (sourceOriginalActualPhysicalDIRTYLaurentRoot434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs V K zeta k R T).coeff d =
    (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      (∑ a : H,
        sourceOriginalActualSignedInitialWeight434
          SP sm BP bm J ell cap hcap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) a *
        (sourceOriginalSignedLaurentDirtyChain434
          (sourceOriginalActualProjectedGEScheduleLaurent434
            SP sm BP bm J ell m cap patterns
            (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
            K zeta k (2*R) T)
          (sourceOriginalActualProjectedGEScheduleLaurent434
            SP sm BP bm J ell m cap patterns
            (fun x z => ¬ sourceOriginalCleanChoice434
              SP sm BP bm J ell m cap patterns x z)
            q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V)
            K zeta k (2*R) T)
          (2*R) 0
          (fun b => AddMonoidAlgebra.single (0:ℤ)
            (sourceOriginalActualSignedProjectedTerminalG434
              SP sm BP bm J ell cap q rho V
              (physicalSourceMuTilde BP bm q (2*R) V)
              (2*R) (2*R)
              (fun out _ => physicalVacuum SP sm BP bm J ell out) b))
          a).coeff d) := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta k N T
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP sm BP bm J ell cap q rho V mu N N
        (fun out _ => physicalVacuum SP sm BP bm J ell out) b)
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let Base : ℂ := physicalSourceBaselineProduct BP bm q N
  change (AddMonoidAlgebra.single (0:ℤ) Base *
    ∑ a : H, AddMonoidAlgebra.single (0:ℤ) (w a) *
      sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a).coeff d =
        Base * ∑ a : H,
          w a * (sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a).coeff d
  rw [source_original_Laurent_single_future_coeff434]
  simp only [sub_zero]
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [source_original_Laurent_single_future_coeff434, sub_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalRootPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 17000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The ORIGINAL physical signed first-DIRTY Memory ROOT, including
all initial Fock masses, complex vacuum, tilted baseline, both OLD
projectors, chronological seen and original joint K, has an EXACT
complex-bilinear CLEAN-prefix / DIRTY / FULL-suffix expansion. -/
theorem source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_prefix_suffix434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    let mu := physicalSourceMuTilde BP bm q (2*R) V
    let Clean := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta k (2*R) T
    let Dirty := sourceOriginalActualSignedProjectedGESchedule434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu K zeta theta k (2*R) T
    let f := sourceOriginalActualSignedProjectedTerminalG434
      SP sm BP bm J ell cap q rho V mu (2*R) (2*R)
      (fun out _ => physicalVacuum SP sm BP bm J ell out)
    let w := sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      ∑ j ∈ Finset.range (2*R), ∑ b : H,
        sourceOriginalSignedForwardPrefix434 Clean j 0 w b *
        sourceOriginalSignedMatrixAction434 (Dirty j)
          (sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 Clean Dirty)
            ((2*R)-(j+1)) (j+1) f) b := by
  dsimp only
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k (2*R) T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k (2*R) T
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu (2*R) (2*R)
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  have hRoot := source_original_ACTUAL_SIGNED_DIRTY_physical_root_matrix_exact434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V K zeta theta k R T hVs hmu
  have hPair := source_original_signed_dirty_prefix_suffix_sum434
    Clean Dirty (2*R) 0 w f
  change sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      (∑ j ∈ Finset.range (2*R), ∑ b : H,
        sourceOriginalSignedForwardPrefix434 Clean j 0 w b *
        sourceOriginalSignedMatrixAction434 (Dirty j)
          (sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 Clean Dirty)
            ((2*R)-(j+1)) (j+1) f) b)
  calc
    _ = (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      (∑ a : H, w a *
        sourceOriginalSignedMatrixDirtyChain434 Clean Dirty (2*R) 0 f a) := hRoot
    _ = _ := by
      rw [hPair]
      simp only [Nat.zero_add]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedWeightedPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Real positive reference density on each of the SAME physical
Fock×seen states. It need not be normalized, and no history is reset. -/
def sourceOriginalSignedJointInverseEnergy434 {H : Type}
    [Fintype H] (π : H → ℝ) (w : H → ℂ) : ℝ :=
  ∑ a : H, (‖w a‖ / Real.sqrt (π a))^2

/-- Original signed suffix quadratic energy against the SAME
positive joint Fock×seen density π, not a history supremum. -/
def sourceOriginalSignedJointForwardEnergy434 {H : Type}
    [Fintype H] (π : H → ℝ) (f : H → ℂ) : ℝ :=
  ∑ a : H, (Real.sqrt (π a) * ‖f a‖)^2

/-- Finite complex-bilinear Cauchy–Schwarz for the ORIGINAL
signed prefix density and its true DIRTY suffix, preserving
the cumulative seen index. No spectral or decay hypothesis. -/
theorem source_original_SIGNED_joint_weighted_CS434
    {H : Type} [Fintype H]
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (w f : H → ℂ) :
    ‖∑ a : H, w a * f a‖ ≤
      Real.sqrt (sourceOriginalSignedJointInverseEnergy434 π w) *
      Real.sqrt (sourceOriginalSignedJointForwardEnergy434 π f) := by
  classical
  let a : H → ℝ := fun x => ‖w x‖ / Real.sqrt (π x)
  let b : H → ℝ := fun x => Real.sqrt (π x) * ‖f x‖
  calc
    _ ≤ ∑ x : H, ‖w x * f x‖ := norm_sum_le _ _
    _ = ∑ x : H, a x * b x := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [a,b]
      rw [norm_mul]
      have hh : Real.sqrt (π x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hπ x))
      field_simp
    _ ≤ Real.sqrt (∑ x : H, a x ^ 2) *
         Real.sqrt (∑ x : H, b x ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPrefixSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Exact conversion between inverse joint Fock density and
the natural direct-density Hilbert norm of the scaled signed prefix. -/
theorem source_original_SIGNED_prefix_inverse_energy_scaled434
    {H : Type} [Fintype H] (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (w : H → ℂ) :
    sourceOriginalSignedJointInverseEnergy434 π w =
      ∑ a : H, π a * ‖w a / (π a : ℂ)‖^2 := by
  classical
  unfold sourceOriginalSignedJointInverseEnergy434
  apply Finset.sum_congr rfl
  intro a ha
  have hp := hπ a
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  rw [div_pow,div_pow,Real.sq_sqrt hp.le]
  field_simp [(ne_of_gt hp)]

/-- The exact ORIGINAL complex CLEAN-prefix transpose has an
inverse-density L² transfer bound from its actual nonnegative
Schur row/column costs. Every joint Fock×seen state is retained.

This lemma does NOT assume Markovness, symmetry, or a spectral gap:
the physical two Schur sums are displayed as explicit premises. -/
theorem source_original_SIGNED_prefix_weighted_Schur434
    {H : Type} [Fintype H] (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (M : H → H → ℂ)
    (C D : ℝ) (hC : 0 ≤ C)
    (hColumn : ∀ b : H, (∑ a : H, π a * ‖M a b‖) ≤ C * π b)
    (hRow : ∀ a : H, (∑ b : H, ‖M a b‖) ≤ D)
    (w : H → ℂ) :
    sourceOriginalSignedJointInverseEnergy434 π
      (sourceOriginalSignedPrefixTranspose434 M w) ≤
    C * D * sourceOriginalSignedJointInverseEnergy434 π w := by
  classical
  let A : H → H → ℝ := fun b a => π a * ‖M a b‖
  let F : H → ℂ := fun a => w a / (π a : ℂ)
  let T : H → ℂ := fun b =>
    sourceOriginalSignedPrefixTranspose434 M w b / (π b : ℂ)
  have hA (b a : H) : 0 ≤ A b a :=
    mul_nonneg (hπ a).le (norm_nonneg _)
  have hRowSchur (b : H) :
      (∑ a : H, A b a) ≤ C * π b := hColumn b
  have hColSchur (a : H) :
      (∑ b : H, A b a) ≤ D * π a := by
    calc
      _ = π a * (∑ b : H, ‖M a b‖) := (Finset.mul_sum ..).symm
      _ ≤ π a * D := mul_le_mul_of_nonneg_left (hRow a) (hπ a).le
      _ = _ := mul_comm _ _
  have hNormScale (b : H) :
      π b * ‖T b‖ = ‖sourceOriginalSignedPrefixTranspose434 M w b‖ := by
    dsimp only [T]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hπ b)]
    field_simp [(ne_of_gt (hπ b))]
  have hTerm (a b : H) :
      A b a * ‖F a‖ = ‖w a * M a b‖ := by
    dsimp only [A,F]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (hπ a),norm_mul]
    field_simp [(ne_of_gt (hπ a))]
  have hTf (b : H) :
      π b * ‖T b‖ ≤ ∑ a : H, A b a * ‖F a‖ := by
    rw [hNormScale]
    change ‖∑ a : H, w a * M a b‖ ≤ _
    calc
      _ ≤ ∑ a : H, ‖w a * M a b‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (hTerm a b).symm
  have hSchur := source_original_finite_density_kernel_energy434
    (Finset.univ : Finset H) π (fun a => (hπ a).le)
    A hA C D hC
    (fun b hb => hRowSchur b)
    (fun a ha => hColSchur a)
    F T (fun b hb => hTf b)
  rw [source_original_SIGNED_prefix_inverse_energy_scaled434
    π hπ (sourceOriginalSignedPrefixTranspose434 M w)]
  rw [source_original_SIGNED_prefix_inverse_energy_scaled434 π hπ w]
  exact hSchur
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPrefixExactSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- An honest finite maximum of the ACTUAL physical weighted
column sums, made total on empty finite H by adjoining none.
No count of numerical histories is multiplied into this maximum. -/
def sourceOriginalSignedColumnSchurMax434
    {H : Type} [Fintype H] (π : H → ℝ) (M : H → H → ℂ) : ℝ :=
  (Finset.univ : Finset (Option H)).sup' Finset.univ_nonempty
    (fun b => match b with
      | none => 0
      | some b => (∑ a : H, π a * ‖M a b‖) / π b)

/-- Actual maximum of COMPLEX absolute CLEAN row sums, with a
zero sentinel but no artificial history-cardinality multiplier. -/
def sourceOriginalSignedRowSchurMax434
    {H : Type} [Fintype H] (M : H → H → ℂ) : ℝ :=
  (Finset.univ : Finset (Option H)).sup' Finset.univ_nonempty
    (fun a => match a with
      | none => 0
      | some a => ∑ b : H, ‖M a b‖)

theorem source_original_SIGNED_column_Schur_max_nonneg434
    {H : Type} [Fintype H] (π : H → ℝ) (M : H → H → ℂ) :
    0 ≤ sourceOriginalSignedColumnSchurMax434 π M := by
  classical
  unfold sourceOriginalSignedColumnSchurMax434
  exact Finset.le_sup' (fun o : Option H => match o with
    | none => 0
    | some b => (∑ a : H, π a * ‖M a b‖) / π b)
    (Finset.mem_univ (none : Option H))

theorem source_original_SIGNED_row_Schur_max_nonneg434
    {H : Type} [Fintype H] (M : H → H → ℂ) :
    0 ≤ sourceOriginalSignedRowSchurMax434 M := by
  classical
  unfold sourceOriginalSignedRowSchurMax434
  exact Finset.le_sup' (fun o : Option H => match o with
    | none => 0
    | some a => ∑ b : H, ‖M a b‖)
    (Finset.mem_univ (none : Option H))

theorem source_original_SIGNED_column_Schur_exact_bound434
    {H : Type} [Fintype H] (π : H → ℝ)
    (hπ : ∀ b, 0 < π b) (M : H → H → ℂ) (b : H) :
    (∑ a : H, π a * ‖M a b‖) ≤
      sourceOriginalSignedColumnSchurMax434 π M * π b := by
  classical
  have h := Finset.le_sup'
    (fun o : Option H => match o with
      | none => 0
      | some b => (∑ a : H, π a * ‖M a b‖) / π b)
    (Finset.mem_univ (some b : Option H))
  change (∑ a : H, π a * ‖M a b‖) / π b ≤
    sourceOriginalSignedColumnSchurMax434 π M at h
  exact (div_le_iff₀ (hπ b)).mp h

theorem source_original_SIGNED_row_Schur_exact_bound434
    {H : Type} [Fintype H] (M : H → H → ℂ) (a : H) :
    (∑ b : H, ‖M a b‖) ≤ sourceOriginalSignedRowSchurMax434 M := by
  classical
  have h := Finset.le_sup'
    (fun o : Option H => match o with
      | none => 0
      | some a => ∑ b : H, ‖M a b‖)
    (Finset.mem_univ (some a : Option H))
  exact h

/-- UNCONDITIONAL numeric cost of the original signed CLEAN
transpose in the inverse true physical Fock/OLD density:
the row and column Schur constants are computed as exact finite
maxima of its ACTUAL joint Fock×seen transition matrix.
No missing hRow, hColumn, unitary or Markov premise. -/
theorem source_original_SIGNED_prefix_exact_Schur434
    {H : Type} [Fintype H] (π : H → ℝ)
    (hπ : ∀ a, 0 < π a)
    (M : H → H → ℂ) (w : H → ℂ) :
    sourceOriginalSignedJointInverseEnergy434 π
      (sourceOriginalSignedPrefixTranspose434 M w) ≤
    sourceOriginalSignedColumnSchurMax434 π M *
      sourceOriginalSignedRowSchurMax434 M *
      sourceOriginalSignedJointInverseEnergy434 π w := by
  exact source_original_SIGNED_prefix_weighted_Schur434
    π hπ M
    (sourceOriginalSignedColumnSchurMax434 π M)
    (sourceOriginalSignedRowSchurMax434 M)
    (source_original_SIGNED_column_Schur_max_nonneg434 π M)
    (source_original_SIGNED_column_Schur_exact_bound434 π hπ M)
    (source_original_SIGNED_row_Schur_exact_bound434 M) w
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedForwardSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The direct signed target energy is exactly a true density
weighted sum of squared complex norms. There is no normalization
of the Fock×seen carrier. -/
theorem source_original_SIGNED_forward_energy_as_sum434
    {H : Type} [Fintype H] (π : H → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π f =
      ∑ a : H,π a * ‖f a‖^2 := by
  classical
  unfold sourceOriginalSignedJointForwardEnergy434
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_pow,Real.sq_sqrt (hπ a)]

/-- Exact genuine finite COMPLEX forward action Schur bound.
The constants are the ORIGINAL weighted column and absolute row
maxima, already used for the signed CLEAN prefix. This is not
a Markov contraction premise and imposes no history independence. -/
theorem source_original_SIGNED_forward_exact_Schur434
    {H : Type} [Fintype H] (π : H → ℝ)
    (hπ : ∀ a, 0 < π a)
    (M : H → H → ℂ) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 π
      (sourceOriginalSignedMatrixAction434 M f) ≤
    sourceOriginalSignedRowSchurMax434 M *
      sourceOriginalSignedColumnSchurMax434 π M *
      sourceOriginalSignedJointForwardEnergy434 π f := by
  classical
  let A : H → H → ℝ := fun a b => π a * ‖M a b‖
  have hA (a b : H) : 0 ≤ A a b :=
    mul_nonneg (hπ a).le (norm_nonneg _)
  have hr (a : H) :
      (∑ b : H,A a b) ≤ sourceOriginalSignedRowSchurMax434 M * π a := by
    change (∑ b : H,π a*‖M a b‖) ≤ _
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left
      (source_original_SIGNED_row_Schur_exact_bound434 M a)
      (hπ a).le).trans_eq (mul_comm _ _)
  have hc (b : H) :
      (∑ a : H,A a b) ≤
      sourceOriginalSignedColumnSchurMax434 π M * π b :=
    source_original_SIGNED_column_Schur_exact_bound434 π hπ M b
  have ht (a : H) :
      π a * ‖sourceOriginalSignedMatrixAction434 M f a‖ ≤
      ∑ b : H,A a b * ‖f b‖ := by
    unfold sourceOriginalSignedMatrixAction434
    calc
      _ ≤ π a * (∑ b : H, ‖M a b*f b‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hπ a).le
      _ = ∑ b : H,A a b * ‖f b‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [norm_mul]
        dsimp [A]
        ring
  have hCore := source_original_finite_density_kernel_energy434
    (Finset.univ : Finset H) π
    (fun a => (hπ a).le) A hA
    (sourceOriginalSignedRowSchurMax434 M)
    (sourceOriginalSignedColumnSchurMax434 π M)
    (source_original_SIGNED_row_Schur_max_nonneg434 M)
    (fun a ha => hr a) (fun b hb => hc b)
    f (sourceOriginalSignedMatrixAction434 M f)
    (fun a ha => ht a)
  rw [source_original_SIGNED_forward_energy_as_sum434
      π (fun a => (hπ a).le)]
  rw [source_original_SIGNED_forward_energy_as_sum434
      π (fun a => (hπ a).le)]
  exact hCore
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualLaurentCoherentFibreDual -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Signed chronological continuation after one TRUE initial
Fock×seen state, restricted to one ACTUAL relative-torus fibre.
The entire path continuation remains ONE coherent COMPLEX sum:
there is no history count, absolute value, or independent future. -/
noncomputable def sourceOriginalSignedCoherentFibreSuffix434
    {H K : Type} [Fintype H] [DecidableEq K]
    (n : ℕ) (key : H × (Fin n → H) → K)
    (U : H → (Fin n → H) → ℂ) (a : H) (rel : K) : ℂ :=
  ∑ tail : Fin n → H,
    if key (a,tail)=rel then U a tail else 0

/-- Exact disintegration of the original COMPLEX chronological
coherent relative-torus amplitude, INITIAL STATE first.
The ORIGINAL source initial vacuum weight stays outside the
coherent continuation; this equality does not replace it by TV. -/
theorem source_original_SIGNED_coherent_fibre_initial_disintegration434
    {H K : Type} [Fintype H] [DecidableEq K]
    (n : ℕ) (key : H × (Fin n → H) → K)
    (w : H → ℂ) (U : H → (Fin n → H) → ℂ) (rel : K) :
    (∑ path ∈ (Finset.univ : Finset (H × (Fin n → H))).filter
      (fun p => key p=rel), w path.1 * U path.1 path.2) =
    ∑ a : H, w a *
      sourceOriginalSignedCoherentFibreSuffix434 n key U a rel := by
  classical
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ tail : Fin n → H,
    if key (a,tail)=rel then w a * U a tail else 0) =
      w a * (∑ tail : Fin n → H,
        if key (a,tail)=rel then U a tail else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail ht
  by_cases h : key (a,tail)=rel <;> simp [h]

/-- An ACTUAL positive density for the true initial Fock×seen
state yields a FINITE weighted coherent-fibre Hilbert bound with
NO multiplicative count of chronological histories. The target
is the signed continuation energy AFTER interference inside each
initial-state fibre, not the TV-square of all paths. -/
theorem source_original_SIGNED_coherent_fibre_dual_CS434
    {H K : Type} [Fintype H] [DecidableEq K]
    (n : ℕ) (key : H × (Fin n → H) → K)
    (π : H → ℝ) (hπ : ∀ a, 0 < π a)
    (w : H → ℂ) (U : H → (Fin n → H) → ℂ) (rel : K) :
    ‖(∑ path ∈ (Finset.univ : Finset (H × (Fin n → H))).filter
      (fun p => key p=rel), w path.1 * U path.1 path.2)‖ ≤
    Real.sqrt (sourceOriginalSignedJointInverseEnergy434 π w) *
      Real.sqrt (sourceOriginalSignedJointForwardEnergy434 π
        (fun a => sourceOriginalSignedCoherentFibreSuffix434 n key U a rel)) := by
  rw [source_original_SIGNED_coherent_fibre_initial_disintegration434]
  exact source_original_SIGNED_joint_weighted_CS434 π hπ w
    (fun a => sourceOriginalSignedCoherentFibreSuffix434 n key U a rel)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPostGhostPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Move the actual signed G factor to the CLEAN prefix, leaving
the literal TWO-SIDED OLD MASKED DIRTY E on the suffix.
This is the required local selector-energy interface: NOT a bound
on the whole G*E row or an independent history approximation. -/
theorem source_original_ACTUAL_signed_post_G_DIRTY_E_pair434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (N i T : ℕ)
    (w f : H → ℂ) :
    (∑ a : H, w a * sourceOriginalSignedMatrixAction434
      (sourceOriginalActualSignedProjectedGEMatrix434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k N i T) f a) =
    ∑ b : H,
      sourceOriginalSignedPrefixTranspose434
        (sourceOriginalActualSignedGhostMatrix434
          SP sm BP bm J ell cap q rho N i V mu) w b *
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T f b := by
  classical
  let G := sourceOriginalActualSignedGhostMatrix434
    SP sm BP bm J ell cap q rho N i V mu
  let EM := sourceOriginalActualSignedOLDMaskedEMatrix434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs V mu K zeta theta o k T
  have hMatrix := source_original_SIGNED_G_E_postghost_pairing434 G EM w f
  change (∑ a : H, w a *
      (∑ c : H, sourceOriginalSignedMatrixProduct434 G EM a c * f c)) =
    ∑ b : H, sourceOriginalSignedPrefixTranspose434 G w b *
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T f b
  calc
    _ = ∑ b : H, sourceOriginalSignedPrefixTranspose434 G w b *
          (∑ c : H, EM b c * f c) := hMatrix
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [←source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs V mu K zeta theta o k T f b]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPostGhostRoot -/

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
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- At insertion index j, move the TRUE signed ghost G_j to the
CLEAN prefix. This is a COMPLEX density on the SAME (Fock,seen)
carrier at the input to the local two-sided OLD-masked DIRTY E_j. -/
def sourceOriginalActualSignedPostGhostPrefix434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N T j : ℕ)
    (w : H → ℂ) : H → ℂ :=
  sourceOriginalSignedPrefixTranspose434
    (sourceOriginalActualSignedGhostMatrix434
      SP sm BP bm J ell cap q rho N j V mu)
    (sourceOriginalSignedForwardPrefix434
      (sourceOriginalActualSignedProjectedGESchedule434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta k N T) j 0 w)

/-- The actual future test AFTER the FIRST DIRTY insertion at j.
It is projected FULL PEP, and the only local operator applied is
the original signed P_T E_DIRTY P_T with the correctly oriented K. -/
def sourceOriginalActualSignedPostGhostDirtySuffix434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N T j : ℕ)
    (f : H → ℂ) : H → ℂ :=
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  sourceOriginalActualSignedOLDMaskedFiniteE434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu
    (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign j))
    zeta theta (physicalAlternatingSign j) k T
    (sourceOriginalSignedMatrixChain434
      (sourceOriginalSignedKernelAdd434 Clean Dirty)
      (N-(j+1)) (j+1) f)

/-- The physical signed DIRTY root rewritten with G_j moved to
the actual complex CLEAN prefix, leaving ONLY the true marked
two-sided OLD-masked DIRTY E_j on the FULL signed suffix. -/
theorem source_original_ACTUAL_signed_physical_root_post_G_pair434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g, 0 < Vs g)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    let mu := physicalSourceMuTilde BP bm q (2*R) V
    let w := sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu
    let f := sourceOriginalActualSignedProjectedTerminalG434
      SP sm BP bm J ell cap q rho V mu (2*R) (2*R)
      (fun out _ => physicalVacuum SP sm BP bm J ell out)
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      ∑ j ∈ Finset.range (2*R), ∑ b : H,
        sourceOriginalActualSignedPostGhostPrefix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k (2*R) T j w b *
        sourceOriginalActualSignedPostGhostDirtySuffix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k (2*R) T j f b := by
  dsimp only
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho V mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs V mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs V mu K zeta theta k N T
  have hRoot := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_prefix_suffix434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs V K zeta theta k R T hVs hmu
  have hVisit (j : ℕ) :
      (∑ a : H, sourceOriginalSignedForwardPrefix434 Clean j 0 w a *
        sourceOriginalSignedMatrixAction434 (Dirty j)
          (sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 Clean Dirty)
            (N-(j+1)) (j+1) f) a) =
      ∑ b : H,
        sourceOriginalActualSignedPostGhostPrefix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T j w b *
        sourceOriginalActualSignedPostGhostDirtySuffix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T j f b := by
    let wj := sourceOriginalSignedForwardPrefix434 Clean j 0 w
    let fj := sourceOriginalSignedMatrixChain434
      (sourceOriginalSignedKernelAdd434 Clean Dirty)
      (N-(j+1)) (j+1) f
    let kj := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign j)
    have hp := source_original_ACTUAL_signed_post_G_DIRTY_E_pair434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu kj zeta theta
      (physicalAlternatingSign j) k N j T wj fj
    exact hp
  change sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q N : ℂ) *
      ∑ j ∈ Finset.range N, ∑ b : H,
        sourceOriginalActualSignedPostGhostPrefix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T j w b *
        sourceOriginalActualSignedPostGhostDirtySuffix434
          SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T j f b
  calc
    _ = (physicalSourceBaselineProduct BP bm q N : ℂ) *
        ∑ j ∈ Finset.range N, ∑ a : H,
          sourceOriginalSignedForwardPrefix434 Clean j 0 w a *
          sourceOriginalSignedMatrixAction434 (Dirty j)
            (sourceOriginalSignedMatrixChain434
              (sourceOriginalSignedKernelAdd434 Clean Dirty)
              (N-(j+1)) (j+1) f) a := hRoot
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hVisit j
end Green64Analytic.CorrelationSquare

end

end

