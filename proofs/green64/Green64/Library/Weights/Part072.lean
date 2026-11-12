module

public import Green64.Library.Weights.Part071
public import Green64.Library.Correlation.Part049
public import Green64.Library.Weights.Part066
public import Green64.Library.Weights.Part067
public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part070
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part014
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part048

@[expose] public section

/-!
# Weights / Part072

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualEFrameSmallSector -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
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
local notation "Frame" => SourceOriginalSourceEFrame434 SP sm BP J ell m patterns

/-- Any NONZERO original source E frame amplitude at its true
integer divisor frequency transports EACH complete SMALL
Haar residue group by the exact signed physical step o*k*D.
Full complex RAW/comparison joint K, the two OLD indices,
theta-independent E coefficient and chronological seen remain
unchanged; zero amplitudes impose no fictional equation. -/
theorem source_original_ACTUAL_E_frame_nonzero_small_transport434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ) (b : H) (r : Frame)
    (hw : sourceOriginalActualFrameThetaWeight434
      SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta o k x seen
      (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
        (sourceOriginalSignedFiniteDelta434 b)) r ≠ 0)
    (g : SG) :
    Green64SmallHaar.residues (sm g) (J+ell) (b.val.1.1 g) =
    Green64SmallHaar.translate (sm g)
      (o*k*(sourceOriginalActualFrameThetaFreq434
        SP sm BP bm J ell m cap patterns x seen o k r : ℤ))
      (Green64SmallHaar.residues (sm g) (J+ell) (x.1 g)) := by
  classical
  by_cases hh : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x seen o k r f
  · let z := sourceOriginalSourceEFrameLift434
      SP sm BP bm J ell m cap patterns x r (Classical.choose hh)
    have hlegal : sourceOrientedPhysicalLegal
        SP sm BP bm J ell m cap patterns x o k z :=
      (Classical.choose_spec hh).1
    have hfreq :
      sourceOriginalActualFrameThetaFreq434
        SP sm BP bm J ell m cap patterns x seen o k r =
        sourceOrientedPhysicalD SP sm BP bm J ell m cap
          (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 := by
      simp [sourceOriginalActualFrameThetaFreq434, hh, z]
    have hk : keep x z := by
      by_contra hn
      have hz : sourceOriginalActualFrameThetaWeight434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta o k x seen
          (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
            (sourceOriginalSignedFiniteDelta434 b)) r = 0 := by
        simp [sourceOriginalActualFrameThetaWeight434, hh, z, hn]
      exact hw hz
    have hdelta :
        sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
          (sourceOriginalSignedFiniteDelta434 b)
          (sourceOrientedPhysicalOutput SP sm BP bm
            J ell m cap patterns x o k z)
          (seen ∪ (orientedEFreshBirths
            SP sm BP bm J ell m cap patterns z).toFinset) ≠ 0 := by
      by_contra hn
      have hz : sourceOriginalActualFrameThetaWeight434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs V mu K zeta o k x seen
          (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
            (sourceOriginalSignedFiniteDelta434 b)) r = 0 := by
        simp [sourceOriginalActualFrameThetaWeight434, hh, hk, z, hn]
      exact hw hz
    have hout := source_original_ACTUAL_history_delta_nonzero_output434
      SP sm BP bm J ell cap b
      (sourceOrientedPhysicalOutput
        SP sm BP bm J ell m cap patterns x o k z)
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
      hdelta
    have ht := source_original_ACTUAL_legal_E_small_torus_transport434
      SP sm BP bm J ell m cap patterns x o k z hlegal g
    rw [hout] at ht
    simpa only [hfreq,sourceOrientedStep] using ht
  · have hz : sourceOriginalActualFrameThetaWeight434
      SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta o k x seen
      (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap
        (sourceOriginalSignedFiniteDelta434 b)) r = 0 := by
      simp [sourceOriginalActualFrameThetaWeight434, hh]
    exact False.elim (hw hz)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualESmallResidueFourierMode -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 25000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The genuine signed Fourier-D coefficient of the ORIGINAL
reachable Fock×seen E matrix vanishes unless every SMALL Haar
residue state at the outgoing endpoint equals the input translated
by the true source o*k*D. This holds for RAW, CLEAN and DIRTY
selectors with arbitrary full joint comparison K and OLD orbit. -/
theorem source_original_ACTUAL_E_Fourier_small_residue_offsector_zero434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (a b : H) (D : ℕ) (g : SG)
    (hbad :
      Green64SmallHaar.residues (sm g) (J+ell) (b.val.1.1 g) ≠
        Green64SmallHaar.translate (sm g) (o*k*(D:ℤ))
          (Green64SmallHaar.residues (sm g) (J+ell) (a.val.1.1 g))) :
    sourceOriginalActualSignedEThetaMode434
      SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta o k a b D = 0 := by
  classical
  unfold sourceOriginalActualSignedEThetaMode434
    sourceOriginalActualFrameThetaDMode434
  apply Finset.sum_eq_zero
  intro r hr
  have hD := (Finset.mem_filter.mp hr).2
  let x := sourceOriginalCanonicalPhysical434
    SP sm BP bm (J+ell) cap a.val.1
  let F := sourceOriginalActualSignedHistoryLift434
    SP sm BP bm J ell cap (sourceOriginalSignedFiniteDelta434 b)
  by_cases hw : sourceOriginalActualFrameThetaWeight434
      SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta o k x a.val.2 F r = 0
  · exact hw
  · have htrans := source_original_ACTUAL_E_frame_nonzero_small_transport434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k x a.val.2 b r hw g
    have hcan : x.1 = a.val.1.1 := rfl
    rw [hD, hcan] at htrans
    exact False.elim (hbad htrans)

/-- The two original OLD masks commute with the above exact SMALL
residue transport restriction, so it survives physical P_T E_i P_T. -/
theorem source_original_ACTUAL_OLD_masked_E_Fourier_small_offsector_zero434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (T : ℕ)
    (a b : H) (D : ℕ) (g : SG)
    (hbad :
      Green64SmallHaar.residues (sm g) (J+ell) (b.val.1.1 g) ≠
        Green64SmallHaar.translate (sm g) (o*k*(D:ℤ))
          (Green64SmallHaar.residues (sm g) (J+ell) (a.val.1.1 g))) :
    sourceOriginalActualSignedOLDMaskedEThetaMode434
      SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta o k T a b D = 0 := by
  unfold sourceOriginalActualSignedOLDMaskedEThetaMode434
  split_ifs <;> first
  | exact source_original_ACTUAL_E_Fourier_small_residue_offsector_zero434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta o k
      a b D g hbad
  | rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGESmallResidueFrequencySupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- A TRUE G_i P_T E_i P_T Fourier coefficient at signed integer
frequency d vanishes unless the resulting SMALL Haar residues are
EXACTLY the input residues translated by d. G_i does not change SMALL
residues, and E_i shifts by its original o*k*D=d. This is a
nontrivial support law for the fully physical finite Fock×seen
matrix, including OLD gating, all RAW/comparison signs and both
BIG/SMALL marked source choices. It is not a saving estimate. -/
theorem source_original_ACTUAL_GE_Fourier_small_torus_offsector_zero434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ) (N i T : ℕ)
    (a c : H) (d : ℤ) (g : SG)
    (hbad :
      Green64SmallHaar.residues (sm g) (J+ell) (c.val.1.1 g) ≠
      Green64SmallHaar.translate (sm g) d
        (Green64SmallHaar.residues (sm g) (J+ell) (a.val.1.1 g))) :
    (sourceOriginalActualProjectedGEThetaLaurent434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta o k N i T a c).coeff d = 0 := by
  classical
  rw [source_original_ACTUAL_projected_GE_Laurent_coeff434]
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro D hD
  by_cases hfreq : o*k*(D:ℤ)=d
  · simp only [if_pos hfreq]
    by_cases hab : a.val.1.1=b.val.1.1
    · have hbadE :
          Green64SmallHaar.residues (sm g) (J+ell) (c.val.1.1 g) ≠
          Green64SmallHaar.translate (sm g) (o*k*(D:ℤ))
            (Green64SmallHaar.residues (sm g) (J+ell) (b.val.1.1 g)) := by
        simpa only [←hfreq, ←hab] using hbad
      have hz := source_original_ACTUAL_OLD_masked_E_Fourier_small_offsector_zero434
        SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
        zeta o k T b c D g hbadE
      rw [hz, mul_zero]
    · have hz := source_original_ACTUAL_G_small_state_offdiag_zero434
        SP sm BP bm J ell cap q rho N i V mu a b hab
      rw [hz, zero_mul]
  · simp only [if_neg hfreq]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSharedSmallDivisor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 23000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Every ORIGINAL shared SMALL prime mark in every group actually
divides the SAME physical divisor D built from all groups' source
endpoint marks and BIG auxiliaries. No legality or extra disjointness
premise is needed: this is the exact source product formula. -/
theorem source_original_ACTUAL_shared_SMALL_label_dvd_D434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (g : SG) (j : Fin (J+ell))
    (hj : j ∈ sourceSmallShared J ell g) :
    sm g (marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j)) ∣
      sourceOrientedPhysicalD SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 := by
  let v := fun h : SG => ∏ j ∈ sourceSmallShared J ell h,
    sm h (marks (sm h) (J+ell) (x.1 h) (z.2.2.2.1 h j))
  have hslot :
      sm g (marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j)) ∣ v g := by
    exact Finset.dvd_prod_of_mem
      (fun i => sm g (marks (sm g) (J+ell) (x.1 g)
        (z.2.2.2.1 g i))) hj
  have hgroup : v g ∣ ∏ h : SG, v h :=
    Finset.dvd_prod_of_mem v (Finset.mem_univ g)
  have hsmall :
      sm g (marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j)) ∣
        ∏ h : SG, v h := dvd_trans hslot hgroup
  change
    sm g (marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j)) ∣
      (∏ h : SG, v h) *
        (∏ h : BG,
          (∏ i ∈ sourceBigShared J ell m (patterns z.1) h,
              bm h ((x.2 h).1 (z.2.2.1.sigmaBig h i))) *
          (∏ j : ↥((patterns z.1).free h), bm h (z.2.1 h j)))
  exact dvd_mul_of_dvd_left hsmall _

/-- Every source shared SMALL mark divides the ACTUAL signed integer
Fourier displacement orientation*k*D as well (not just the divisor).
Thus this shared coordinate does not move under a legal source E. -/
theorem source_original_ACTUAL_shared_SMALL_label_dvd_step434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (g : SG) (j : Fin (J+ell))
    (hj : j ∈ sourceSmallShared J ell g) :
    (sm g (marks (sm g) (J+ell) (x.1 g)
      (z.2.2.2.1 g j)) : ℤ) ∣
      sourceOrientedStep SP sm BP bm J ell m cap
        (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k := by
  obtain ⟨t,ht⟩ := source_original_ACTUAL_shared_SMALL_label_dvd_D434
    SP sm BP bm J ell m cap patterns x z g j hj
  refine ⟨o*k*(t:ℤ), ?_⟩
  unfold sourceOrientedStep
  rw [ht]
  push_cast
  ring

/-- A LEGAL original oriented source physical edge keeps every
permuted source shared mark identical to the corresponding target
mark, and that COMMON prime itself divides D. It is stronger than
the previous bare Haar residue transport theorem. -/
theorem source_original_ACTUAL_legal_shared_SMALL_mark_and_divisor434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal
      SP sm BP bm J ell m cap patterns x o k z)
    (g : SG) (j : Fin (J+ell))
    (hj : j ∈ sourceSmallShared J ell g) :
    let p := sm g (marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j))
    marks (sm g) (J+ell) (x.1 g) (z.2.2.2.1 g j) =
      marks (sm g) (J+ell)
        ((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap
          patterns x o k z).1 g) (z.2.2.2.2 g j) ∧
    p ∣ sourceOrientedPhysicalD SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 := by
  dsimp only
  constructor
  · exact (hlegal.2.2.2.2 g).2 j hj
  · exact source_original_ACTUAL_shared_SMALL_label_dvd_D434
      SP sm BP bm J ell m cap patterns x z g j hj
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallTorusLaurentTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- Arithmetic small-residue compatibility for an individual
signed Laurent coefficient, between two fixed genuine Haar torus
residue states. This predicate is a SUPPORT restriction, not
a positivity, cancellation or norm statement. -/
def sourceOriginalLaurentSmallTransport434
    (a b : Green64SmallHaar.SmallTorus modulus)
    (M : AddMonoidAlgebra ℂ ℤ) : Prop :=
  ∀ d, b ≠ Green64SmallHaar.translate modulus d a → M.coeff d=0

theorem source_original_Laurent_small_transport_zero434
    (a b : Green64SmallHaar.SmallTorus modulus) :
    sourceOriginalLaurentSmallTransport434 modulus a b 0 := by
  intro d hd
  simp [AddMonoidAlgebra.coeff_zero]

theorem source_original_Laurent_small_transport_add434
    (a b : Green64SmallHaar.SmallTorus modulus)
    (M N : AddMonoidAlgebra ℂ ℤ)
    (hM : sourceOriginalLaurentSmallTransport434 modulus a b M)
    (hN : sourceOriginalLaurentSmallTransport434 modulus a b N) :
    sourceOriginalLaurentSmallTransport434 modulus a b (M+N) := by
  intro d hd
  rw [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hM d hd,hN d hd]
  simp

/-- Exact additive SMALL torus holonomy: if P transports residues
a→b and Q transports b→c, their actual Laurent product transports
a→c by the SUM of the two signed physical frequencies.
No assumption of independent ghosts or separate phases. -/
theorem source_original_Laurent_small_transport_mul434
    (a b c : Green64SmallHaar.SmallTorus modulus)
    (M N : AddMonoidAlgebra ℂ ℤ)
    (hM : sourceOriginalLaurentSmallTransport434 modulus a b M)
    (hN : sourceOriginalLaurentSmallTransport434 modulus b c N) :
    sourceOriginalLaurentSmallTransport434 modulus a c (M*N) := by
  intro d hbad
  rw [source_original_Laurent_actual_coeff_mul434]
  apply Finset.sum_eq_zero
  intro e he
  by_cases heq : b=Green64SmallHaar.translate modulus e a
  · have htail : c ≠
        Green64SmallHaar.translate modulus (d-e) b := by
      intro hc
      apply hbad
      calc
        c = Green64SmallHaar.translate modulus (d-e) b := hc
        _ = Green64SmallHaar.translate modulus (d-e)
              (Green64SmallHaar.translate modulus e a) := by rw [heq]
        _ = Green64SmallHaar.translate modulus d a := by
          funext p
          simp only [Green64SmallHaar.translate,Int.cast_sub]
          push_cast
          abel
    rw [hN (d-e) htail,mul_zero]
  · rw [hM e heq,zero_mul]

/-- The true terminal observable of the physical signed root
has frequency ZERO before applying E_i phases. Any such frequency
zero-only terminal multiplier respects unchanged SMALL residues. -/
theorem source_original_Laurent_small_transport_terminal_zero434
    (a : Green64SmallHaar.SmallTorus modulus)
    (z : ℂ) :
    sourceOriginalLaurentSmallTransport434 modulus a a
      (AddMonoidAlgebra.single (0:ℤ) z) := by
  intro d hd
  have hn : d ≠ 0 := by
    intro he
    apply hd
    subst d
    exact (Green64SmallHaar.translate_zero modulus a).symm
  rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  simp [Ne.symm hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallTorusPathTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The ACTUAL terminal state of an ordered Fock×seen path.
This is the last chronological state, not a fresh independent
terminal variable or an arbitrary residue test. -/
def sourceOriginalSignedLaurentPathTerminal434
    {H : Type} : (n : ℕ) → (a : H) → (Fin n → H) → H
  | 0, a, _ => a
  | n+1, _, path =>
      sourceOriginalSignedLaurentPathTerminal434 n (path 0)
        (Fin.tail path)

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable {H : Type} [Fintype H] (res : H → Green64SmallHaar.SmallTorus modulus)

/-- Every TRUE chronological state-path multiplication preserves
its SMALL Haar torus shift by the SUM of local integer Fourier
frequencies, provided its source edges do. This theorem never
assumes no-rebirth or imaginary independence of the Fock states. -/
theorem source_original_Laurent_small_path_transport434
    (M : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (hM : ∀ i a b,
      sourceOriginalLaurentSmallTransport434 modulus
        (res a) (res b) (M i a b))
    (hf : ∀ a,
      sourceOriginalLaurentSmallTransport434 modulus
        (res a) (res a) (f a))
    (n start : ℕ) (a : H) (path : Fin n → H) :
    sourceOriginalLaurentSmallTransport434 modulus
      (res a)
      (res (sourceOriginalSignedLaurentPathTerminal434 n a path))
      (sourceOriginalSignedLaurentPathWeight434 M f n start a path) := by
  induction n generalizing start a with
  | zero => exact hf a
  | succ n ih =>
      change sourceOriginalLaurentSmallTransport434 modulus
        (res a)
        (res (sourceOriginalSignedLaurentPathTerminal434
          n (path 0) (Fin.tail path)))
        (M start a (path 0) *
          sourceOriginalSignedLaurentPathWeight434
            M f n (start+1) (path 0) (Fin.tail path))
      exact source_original_Laurent_small_transport_mul434 modulus
        (res a) (res (path 0))
        (res (sourceOriginalSignedLaurentPathTerminal434
          n (path 0) (Fin.tail path)))
        (M start a (path 0))
        (sourceOriginalSignedLaurentPathWeight434
          M f n (start+1) (path 0) (Fin.tail path))
        (hM start a (path 0))
        (ih (start+1) (path 0) (Fin.tail path))

/-- The ACTUAL first-DIRTY chronology inherits the same modular
frequency constraint for every individual REAL state path.
The first DIRTY insertion is summed coherently within a fixed
ordered Fock×seen history; CLEAN and FULL continuations have
identical small-residue transport support. -/
theorem source_original_Laurent_small_DIRTY_path_transport434
    (C D : ℕ → H → H → AddMonoidAlgebra ℂ ℤ)
    (f : H → AddMonoidAlgebra ℂ ℤ)
    (hC : ∀ i a b,
      sourceOriginalLaurentSmallTransport434 modulus
        (res a) (res b) (C i a b))
    (hD : ∀ i a b,
      sourceOriginalLaurentSmallTransport434 modulus
        (res a) (res b) (D i a b))
    (hf : ∀ a,
      sourceOriginalLaurentSmallTransport434 modulus
        (res a) (res a) (f a))
    (n start : ℕ) (a : H) (path : Fin n → H) :
    sourceOriginalLaurentSmallTransport434 modulus
      (res a)
      (res (sourceOriginalSignedLaurentPathTerminal434 n a path))
      (sourceOriginalSignedLaurentDirtyPathWeight434
        C D f n start a path) := by
  induction n generalizing start a with
  | zero =>
      exact source_original_Laurent_small_transport_zero434 modulus _ _
  | succ n ih =>
      change sourceOriginalLaurentSmallTransport434 modulus
        (res a)
        (res (sourceOriginalSignedLaurentPathTerminal434
          n (path 0) (Fin.tail path)))
        (D start a (path 0) *
            sourceOriginalSignedLaurentPathWeight434
              (fun i x y => C i x y + D i x y)
              f n (start+1) (path 0) (Fin.tail path) +
          C start a (path 0) *
            sourceOriginalSignedLaurentDirtyPathWeight434
              C D f n (start+1) (path 0) (Fin.tail path))
      apply source_original_Laurent_small_transport_add434 modulus
      · exact source_original_Laurent_small_transport_mul434 modulus
          (res a) (res (path 0))
          (res (sourceOriginalSignedLaurentPathTerminal434
            n (path 0) (Fin.tail path)))
          (D start a (path 0))
          (sourceOriginalSignedLaurentPathWeight434
            (fun i x y => C i x y + D i x y)
            f n (start+1) (path 0) (Fin.tail path))
          (hD start a (path 0))
          (source_original_Laurent_small_path_transport434 modulus res
            (fun i x y => C i x y + D i x y) f
            (fun i x y => source_original_Laurent_small_transport_add434
              modulus (res x) (res y) (C i x y) (D i x y)
              (hC i x y) (hD i x y))
            hf n (start+1) (path 0) (Fin.tail path))
      · exact source_original_Laurent_small_transport_mul434 modulus
          (res a) (res (path 0))
          (res (sourceOriginalSignedLaurentPathTerminal434
            n (path 0) (Fin.tail path)))
          (C start a (path 0))
          (sourceOriginalSignedLaurentDirtyPathWeight434
            C D f n (start+1) (path 0) (Fin.tail path))
          (hC start a (path 0))
          (ih (start+1) (path 0) (Fin.tail path))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDIRTYSmallTorusPaths -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The TRUE chronological CLEAN-before-DIRTY/FULL-after signed
physical path amplitude at total Fourier frequency d vanishes
unless the FINAL reachable SMALL Haar residue group equals the
INITIAL residue group shifted by EXACTLY d (mod every p in group).
All original G/E, all previous birth history, alternate orientations,
both OLD projectors and one joint RAW/comparison K are preserved.
The terminal SMALL boundary is not fixed, so this gives a true
selection rule, NOT automatic global signed-memory saving. -/
theorem source_original_ACTUAL_PHYSICAL_DIRTY_path_small_torus_selection434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (R T : ℕ)
    (g : SG) (a : H) (path : Fin (2*R) → H) (d : ℤ)
    (hbad :
      Green64SmallHaar.residues (sm g) (J+ell)
        ((sourceOriginalSignedLaurentPathTerminal434 (2*R) a path).val.1.1 g) ≠
      Green64SmallHaar.translate (sm g) d
        (Green64SmallHaar.residues (sm g) (J+ell) (a.val.1.1 g))) :
    (sourceOriginalSignedLaurentDirtyPathWeight434
      (sourceOriginalActualProjectedGEScheduleLaurent434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V
        (physicalSourceMuTilde BP bm q (2*R) V)
        K zeta k (2*R) T)
      (sourceOriginalActualProjectedGEScheduleLaurent434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs V
        (physicalSourceMuTilde BP bm q (2*R) V)
        K zeta k (2*R) T)
      (fun b => AddMonoidAlgebra.single (0:ℤ)
        (sourceOriginalActualSignedProjectedTerminalG434
          SP sm BP bm J ell cap q rho V
          (physicalSourceMuTilde BP bm q (2*R) V)
          (2*R) (2*R)
          (fun out _ => physicalVacuum SP sm BP bm J ell out) b))
      (2*R) 0 a path).coeff d = 0 := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let res : H → Green64SmallHaar.SmallTorus (sm g) :=
    fun v => Green64SmallHaar.residues (sm g) (J+ell) (v.val.1.1 g)
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
  have hC (i : ℕ) (u v : H) :
      sourceOriginalLaurentSmallTransport434 (sm g)
        (res u) (res v) (C i u v) := by
    intro freq hf
    exact source_original_ACTUAL_GE_Fourier_small_torus_offsector_zero434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta (physicalAlternatingSign i) k N i T u v freq g hf
  have hD (i : ℕ) (u v : H) :
      sourceOriginalLaurentSmallTransport434 (sm g)
        (res u) (res v) (D i u v) := by
    intro freq hf
    exact source_original_ACTUAL_GE_Fourier_small_torus_offsector_zero434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
      zeta (physicalAlternatingSign i) k N i T u v freq g hf
  have hF (b : H) :
      sourceOriginalLaurentSmallTransport434 (sm g)
        (res b) (res b) (F b) :=
    source_original_Laurent_small_transport_terminal_zero434 (sm g)
      (res b) _
  exact source_original_Laurent_small_DIRTY_path_transport434
    (sm g) res C D F hC hD hF N 0 a path d hbad
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYSmallTorusSelection -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- Original source03 true signed path amplitude at TOTAL Fourier
frequency d vanishes unless every SMALL modular group g follows
the exact global Haar residue transport. In particular this
applies to the original distinguished group S and EVERY Ts group,
with actual all-Tb births and original full joint RAW/comparison K.
No new source03 admissibility or smallness assumptions. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_path_small_residue_offsector_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (g : Option ι)
    (path : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d : ℤ)
    (hbad :
      Green64SmallHaar.residues
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        (J+ell)
        ((sourceOriginalSignedLaurentPathTerminal434 (2*R)
          path.1 path.2).val.1.1 g) ≠
      Green64SmallHaar.translate
        (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
        d
        (Green64SmallHaar.residues
          (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} => p.val)
          (J+ell) (path.1.val.1.1 g))) :
    sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T path d = 0 := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1
      g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  have hh := source_original_ACTUAL_PHYSICAL_DIRTY_path_small_torus_selection434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl)
    cfg.q0 rho Vs u.Vbig K zeta k R T
    g path.1 path.2 d hbad
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let w := sourceOriginalActualSignedInitialWeight434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    (fun _ => le_rfl) Vs mu
  have hm : w path.1 *
      (sourceOriginalSignedLaurentDirtyPathWeight434
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m (fun g => Fintype.card (BP g))
          (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          (sourceOriginalCleanChoice434 SP (fun _ p => p.val)
            BP (fun _ p => p.val) J ell m
            (fun g => Fintype.card (BP g))
            (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ))
          cfg.q0 rho Vs u.Vbig mu K zeta k (2*R) T)
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m (fun g => Fintype.card (BP g))
          (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell m (fun g => Fintype.card (BP g))
            (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) x z)
          cfg.q0 rho Vs u.Vbig mu K zeta k (2*R) T)
        (fun b => AddMonoidAlgebra.single (0:ℤ)
          (sourceOriginalActualSignedProjectedTerminalG434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell (fun g => Fintype.card (BP g))
            cfg.q0 rho u.Vbig mu (2*R) (2*R)
            (fun out _ => physicalVacuum
              SP (fun _ p => p.val) BP (fun _ p => p.val) J ell out) b))
        (2*R) 0 path.1 path.2).coeff d = 0 := by
    rw [hh,mul_zero]
  convert hm using 1
  all_goals try rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSignedDIRTYEnergy -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The two ORIGINAL moving S+Ts/Tb source energies, using exact
source q0, joint RAW/comparison K, 2R visits, chronological seen,
both OLD projectors and real physical Fock/sector densities. -/
def sourceOriginalActualSourceSignedDIRTYEnergyPair434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℝ × ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  exact sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig K zeta theta k R T

/-- The TRUE original source physical first-DIRTY root has a
quantitative bound through precisely defined dual source energies.
NO new global energy bound is presumed. -/
theorem source_original_ACTUAL_SOURCE_signed_DIRTY_energy_norm434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceMuTilde (fun g => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) u.Vbig g p) :
    ‖sourceOriginalActualSourcePhysicalDIRTYRoot434 u blockA blockB
      J ell m hmJ Q hA hB xi rho zeta theta k R T‖ ≤
    ‖(physicalSourceBaselineProduct
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖ *
    Real.sqrt ((sourceOriginalActualSourceSignedDIRTYEnergyPair434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T).1) *
    Real.sqrt ((sourceOriginalActualSourceSignedDIRTYEnergyPair434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T).2) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hVb (g : β) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have h := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_energy_norm434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig hVs hVb
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi)
    zeta theta k R T hmu
  simpa only [sourceOriginalActualSourcePhysicalDIRTYRoot434,
    sourceOriginalActualSourceSignedDIRTYEnergyPair434,SP,BP,P,Vs] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSignedSchurBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Actual moving source03 S+Ts/Tb CLEAN Schur prefix budget,
computed from the canonical RAW/comparison K, the original Fock
orbit masses and genuine chronological seen states. -/
def sourceOriginalActualSourceCLEANSchurSum434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
    J ell m hmJ Q hA hB xi
  exact sourceOriginalActualPhysicalCLEANSchurSum434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    cfg.q0 rho Vs u.Vbig K zeta theta k R T

/-- Exact ORIGINAL source first-vacuum Fock energy, no forced
unit normalization and no artificial history multiplicity. -/
def sourceOriginalActualSourceInitialVacuumEnergy434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) (R : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  exact sourceOriginalActualPhysicalInitialVacuumEnergy434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    (sourceOriginalActualSmallMass434 u)
    (physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0 (2*R) u.Vbig)

/-- The literal physical first-DIRTY root on the TRUE moving source
S+Ts/Tb is bounded without any separate prefix-energy hypothesis:
only the computed CLEAN Schur products, true initial vacuum mass and
the original actual DIRTY target quadratic energy remain. -/
theorem source_original_ACTUAL_SOURCE_signed_DIRTY_Schur_bound434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceMuTilde (fun g => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) u.Vbig g p) :
    ‖sourceOriginalActualSourcePhysicalDIRTYRoot434 u blockA blockB
      J ell m hmJ Q hA hB xi rho zeta theta k R T‖ ≤
    ‖(physicalSourceBaselineProduct
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖ *
    Real.sqrt
      (sourceOriginalActualSourceCLEANSchurSum434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T *
       sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R) *
    Real.sqrt
      ((sourceOriginalActualSourceSignedDIRTYEnergyPair434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta theta k R T).2) := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hVb (g : β) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have h := source_original_ACTUAL_PHYSICAL_signed_DIRTY_Schur_energy434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m (fun g => Fintype.card (BP g))
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    hi (fun _ => le_rfl) cfg.q0 rho Vs u.Vbig hVs hVb
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta k R T hmu
  simpa only [sourceOriginalActualSourcePhysicalDIRTYRoot434,
    sourceOriginalActualSourceCLEANSchurSum434,
    sourceOriginalActualSourceInitialVacuumEnergy434,
    sourceOriginalActualSourceSignedDIRTYEnergyPair434,
    SP,BP,P,Vs] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSignedInitialBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The real source03 S+Ts initial dual energy of the full
complex Fock×chronological-history initial prefix, with all
actual SMALL masses and tilted BIG prime masses. -/
def sourceOriginalActualSourceSignedInitialDualEnergy434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap := fun g : β => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedTruePrefixEnergy434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap Vs u.Vbig mu
    (sourceOriginalActualSignedInitialWeight434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
      (fun _ => le_rfl) Vs mu)

/-- The actual total SMALL Haar/mark mass of all S+Ts groups.
No pretend normalization: for J+ell positive it need not equal one. -/
def sourceOriginalActualSourceSignedInitialSmallMass434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  exact ∑ s : GroupState SP (fun _ p => p.val) (J+ell),
    groupStateMass SP (fun _ p => p.val) (J+ell) Vs

/-- The initial signed source Fock dual energy with the true BIG
baseline is paid by the exact SMALL S+Ts Haar state mass alone.
This applies to the original moving source data at R=ceil L^.52,
assuming its TRUE harmonic BIG law and BIG lower prime scale.
NO independent initial-energy or history bound is supplied. -/
theorem eventually_source_original_ACTUAL_SOURCE_signed_initial_budget434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β] {x Y Hp : ℝ}
      (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},
          1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
          Real.exp (L^cfg.cexp) ≤ (p.val:ℝ)),
      let R := Nat.ceil (L^(0.52:ℝ))
      let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
      ‖(physicalSourceBaselineProduct BP (fun _ p => p.val)
          cfg.q0 (2*R):ℂ)‖ *
        sourceOriginalActualSourceSignedInitialDualEnergy434 u J ell R ≤
      sourceOriginalActualSourceSignedInitialSmallMass434 u J ell := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [eventually_source_original_B26_visits_below_BIG434
    cfg.cexp hc] with L hVisits
  intro ι β _ _ _ _ x Y Hp u hHarmonic hmin
  dsimp only
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let R := Nat.ceil (L^(0.52:ℝ))
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hV (g : β) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have hb (g : β) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    have h := (source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))).1
    linarith
  have hb1 (g : β) (p : BP g) :
      physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p ≤ 1 :=
    (source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))).2
  have h := source_original_ACTUAL_initial_signed_prefix_budget434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g)) (fun _ => le_rfl)
    cfg.q0 Vs u.Vbig hVs hV hHarmonic R hb hb1
  simpa only [sourceOriginalActualSourceSignedInitialDualEnergy434,
    sourceOriginalActualSourceSignedInitialSmallMass434,
    SP,BP,P,Vs,R] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallGroupHarmonicNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (M : ℕ)

/-- FULL original tensor of SMALL Haar / ordered distinct marks has
total mass at most ONE under genuine harmonic V_g=sum_p 1/p.
The SMALL groups are independent only in their ORIGINAL product
Haar measure; no cross-group M! or fictitious Markov law appears. -/
theorem source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (hHarmonic : ∀ g, Vs g = ∑ p : SP g,1/(sm g p:ℝ)) :
    (∑ s : GroupState SP sm M,groupStateMass SP sm M Vs) ≤ 1 := by
  classical
  have hFactor :
      (∑ s : GroupState SP sm M,groupStateMass SP sm M Vs) =
      ∏ g : SG, ∑ x : SmallState (sm g) M,
        stateMass (sm g) M (Vs g) := by
    unfold groupStateMass
    simpa using (Fintype.prod_sum
      (f := fun (g : SG) (_x : SmallState (sm g) M) =>
        stateMass (sm g) M (Vs g))).symm
  rw [hFactor]
  calc
    _ ≤ ∏ _g : SG,(1:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        apply Finset.sum_nonneg
        intro x hx
        exact (stateMass_positive (sm g) M (Vs g) (hVs g)).le
      · intro g hg
        exact source_original_ACTUAL_SMALL_state_harmonic_mass_le_one434
          (sm g) M (Vs g) (hVs g) (hHarmonic g)
    _ = 1 := by simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceSmallHarmonicNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The missing ORIGINAL source03 normalization for the SINGLE
distinguished small group S and EVERY other small group Ts.
These are exact harmonic equalities; SourceComparisonData434
does not currently contain them as fields. -/
def SourceOriginalActualSourceSMALLHarmonic434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) : Prop :=
  ∀ g : Option ι, sourceOriginalActualSmallMass434 u g =
    ∑ p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g},
      (1:ℝ)/(p.val:ℝ)

/-- For the full S+Ts Haar carrier, the exact source harmonic
equalities imply TOTAL marked-state mass <= 1, uniformly in
J, ell, the number of groups and moving prime alphabets. -/
theorem source_original_ACTUAL_SOURCE_SMALL_harmonic_mass_le_one434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ)
    (hHarmonic : SourceOriginalActualSourceSMALLHarmonic434 u) :
    sourceOriginalActualSourceSignedInitialSmallMass434 u J ell ≤ 1 := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1
      g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le
      ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hP (g : Option ι) :
      Vs g = ∑ p : SP g, (1:ℝ)/(p.val:ℝ) := by
    exact hHarmonic g
  have h := source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
    SP (fun _ p => p.val) (J+ell) Vs hVs hP
  simpa only [sourceOriginalActualSourceSignedInitialSmallMass434,
    SP,P,Vs] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03PrimeSliceSmallHarmonicBridge -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 250000

variable {n : ℕ} {cfg : SourceComparisonFixed434}
variable {L d vmax c0 x Y Hp : ℝ}
variable (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
variable (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)

/-- The physical SMALL Source03 harmonic normalization is no
longer an independent hypothesis once the canonical verified
group fields have been installed. This makes the actual
sourceOriginalActualSourceSMALLHarmonic434 true at each
distinguished S and Ts group. -/
theorem source_original_canonical_fields_small_harmonic434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    SourceOriginalActualSourceSMALLHarmonic434 u := by
  rcases h with ⟨hS,hTs,_,hVs,hVsmall,_⟩
  intro g
  cases g with
  | none =>
      change u.Vs =
        ∑ p : {p : ℕ // p∈u.S}, (1:ℝ)/(p.val:ℝ)
      rw [hVs,hS,source_original_canonical_FINSET_subtype_harmonic434]
      exact (z.exact_SMALL_harmonic434).1
  | some i =>
      change u.Vsmall i =
        ∑ p : {p : ℕ // p∈u.Ts i}, (1:ℝ)/(p.val:ℝ)
      rw [hVsmall,hTs,source_original_canonical_FINSET_subtype_harmonic434]
      exact (z.exact_SMALL_harmonic434).2 i
/-- Real original source03 SMALL Fock initial mass is <=1 when
the comparison data USES THE CONSTRUCTED prime groups. The
previous mass theorem demanded a free exact-harmonic hypothesis;
that hypothesis is now discharged by the real arithmetic
prime-family constructor and the strict group-field match. -/
theorem source_original_canonical_fields_true_initial_Fock_mass_le_one434
    (h : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (J ell : ℕ) :
    sourceOriginalActualSourceSignedInitialSmallMass434 u J ell ≤ 1 :=
  source_original_ACTUAL_SOURCE_SMALL_harmonic_mass_le_one434
    u J ell (source_original_canonical_fields_small_harmonic434 z u h)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHarmonicPhysicalInitial -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Under ORIGINAL harmonic source masses for BOTH SMALL and BIG,
the true BIG baseline times initial Fock/vacuum energy is <= ONE.
This uses the exact finite 0/1 vacuum and global numeric Nodup
birth gate; no Fock/history multiplicity survives. -/
theorem source_original_ACTUAL_physical_initial_harmonic_mass_le_one434
    (q : ℝ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (hSmall : ∀ g,Vs g = ∑ p : SP g,1/(sm g p:ℝ))
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hBig : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=Vb g)
    (R : ℕ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP sm BP bm J ell cap Vs
          (physicalSourceMuTilde BP bm q (2*R) Vb) ≤ 1 := by
  have hmu (g : BG) (p : BP g) :
      0 < physicalSourceMuTilde BP bm q (2*R) Vb g p := by
    have hp : (0:ℝ) < (bm g p:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos (bm g p))
    have hv := hVb g
    have hbp := hb g p
    dsimp only [physicalSourceMuTilde]
    positivity
  have hMass := source_original_ACTUAL_initial_mass_le_SMALL_mass434
    SP sm BP bm J ell cap q Vs hVs Vb hVb hBig R hb hb1
  have hEq := source_original_ACTUAL_initial_mass_eq_signed_good_mass434
    SP sm BP bm J ell cap q Vs Vb R hVs hmu
  have hHaar := source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
    SP sm (J+ell) Vs hVs hSmall
  calc
    _ = sourceOriginalActualInitialVacuumMass434
          SP sm BP bm J ell cap q Vs Vb R := by
      rw [source_original_ACTUAL_physical_initial_vacuum_energy_eq_good434]
      exact hEq.symm
    _ ≤ ∑ s : GroupState SP sm (J+ell),
      groupStateMass SP sm (J+ell) Vs := hMass
    _ ≤ 1 := hHaar
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalComparisonReplace -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- Install the ACTUALLY CONSTRUCTED original S+Ts+FULL-Tb prime
families into the UNCHANGED source03 comparison record, preserving
every endpoint datum other than the original prime groups and their
harmonic normalizations and the selected parity support.
This requires only the ORIGINAL endpoint's S<=Ncap size condition
and Ptw subset of the new true prime union; no arbitrary extra
group disjointness or harmonic assumptions survive. -/
noncomputable def sourceOriginalCanonicalComparisonReplaceGroups434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 1 < L) (hd : d < (1/2:ℝ))
    (hcd : cfg.cexp < d)
    (hSN : ∀ p∈z.S, p ≤ u.Ncap)
    (PtwNew : Finset ℕ) (hParityNew : PtwNew ⊆ z.G) :
    SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp := by
  let hs := z.source_group_membership_and_disjoint434
  refine { u with
    G := z.G
    Ptw := PtwNew
    S := z.S
    Ts := z.Ts
    Tb := z.Tb
    Vs := z.Vs
    Vsmall := z.Vsmall
    Vbig := z.Vbig
    hVs := (z.hSmallMass none).1
    hVsmall := (fun i => (z.hSmallMass (some i)).1)
    hVbig := (fun i => (z.hBigMass i).1)
    hSG := hs.1
    hSPrime := hs.2.1
    hSN := hSN
    hGroup := z.physical_G_below_sqrt434 hL hd hcd
    hSmall := (fun p hp => (z.hSmallBand none p hp).2)
    hG := rfl
    hParity := hParityNew
    hTsPrime := hs.2.2.1
    hTbPrime := hs.2.2.2.1
    hDisjS := hs.2.2.2.2.1
    hDisjB := hs.2.2.2.2.2.1 }

/-- This is a concrete implementation, not a new set of
independently assumed group fields: the unchanged original
SOURCE comparison record after replacing groups agrees with
the certified canonical source slice field-for-field. -/
theorem source_original_canonical_replacement_real_fields434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 1<L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (hSN : ∀ p∈z.S, p≤u.Ncap)
    (PtwNew : Finset ℕ) (hParityNew : PtwNew⊆z.G) :
    SourceOriginalSource03CanonicalFieldsMatch434 z
      (sourceOriginalCanonicalComparisonReplaceGroups434
        z u hL hd hcd hSN PtwNew hParityNew) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalComparisonLargeL -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 220000

/-- For L>=4 the original u.Ncap is ALREADY large enough to
contain ALL certified moving source03 SMALL and BIG prime labels.
This discharges the last physical S<=Ncap prerequisite for
replacing the genuine comparison endpoint's group prime universe. -/
theorem source_original_canonical_large_L_all_groups_below_Ncap434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d) :
    ∀ p ∈ z.G, p ≤ u.Ncap := by
  have hLpos : 0 ≤ L := by linarith
  have hsqrt : (Real.sqrt L)^2=L := Real.sq_sqrt hLpos
  have hh : 0 ≤ L*(L-4) :=
    mul_nonneg hLpos (by linarith)
  have hs : Real.sqrt L ≤ L/2 := by
    nlinarith [Real.sqrt_nonneg L]
  have hroot : Real.sqrt L ≤ 3*L/4 := by
    linarith
  have hy0 : 0 ≤ Y := by linarith [u.hY]
  have hY : Y ≤ cfg.A*Y := by
    have hx : 0 ≤ (cfg.A-1)*Y :=
      mul_nonneg (by linarith [cfg.hA]) hy0
    nlinarith
  have hCap :
      Real.exp (Real.sqrt L) ≤ (u.Ncap:ℝ) :=
    (Real.exp_le_exp.mpr hroot).trans
      (u.hYstrong.trans (hY.trans u.hCap))
  intro p hp
  have hG := z.physical_G_below_sqrt434
    (by linarith : 1<L) hd hcd p hp
  exact_mod_cast (hG.trans hCap)

/-- Install the ACTUAL canonical prime groups for the original
un-twisted epsilon=1 endpoint, WITH ALL real SourceComparisonData
fields intact and WITHOUT any new geometric or mass hypothesis. -/
noncomputable def sourceOriginalCanonicalComparisonUntwisted434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d) :
    SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp :=
  sourceOriginalCanonicalComparisonReplaceGroups434 z u
    (by linarith : 1<L) hd hcd
    (fun p hp =>
      source_original_canonical_large_L_all_groups_below_Ncap434
        z u hL hd hcd p ((z.source_group_membership_and_disjoint434).1 hp))
    ∅ (Finset.empty_subset _)

/-- Install the original FULL completely-multiplicative parity
twist epsilon=(-1)^sum_{p in all TRUE group primes}v_p(n).
The twist is supported on the ACTUAL S+Ts+FULL-Tb union and not
a fabricated or independent random-sign prime set. -/
noncomputable def sourceOriginalCanonicalComparisonFullTwist434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d) :
    SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp :=
  sourceOriginalCanonicalComparisonReplaceGroups434 z u
    (by linarith : 1<L) hd hcd
    (fun p hp =>
      source_original_canonical_large_L_all_groups_below_Ncap434
        z u hL hd hcd p ((z.source_group_membership_and_disjoint434).1 hp))
    z.G Finset.Subset.rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalComparisonParity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 260000

/-- The TWO genuine source03 parity choices of the SAME concrete
original comparison datum. All group primes belong to the REAL
canonical S+Ts+FULL-Tb family; eps=false means no parity twist,
eps=true means twisting by ALL genuine group primes. -/
noncomputable def sourceOriginalCanonicalComparisonParityChoice434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) :
    SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp :=
  if eps then
    sourceOriginalCanonicalComparisonFullTwist434 z u hL hd hcd
  else
    sourceOriginalCanonicalComparisonUntwisted434 z u hL hd hcd

/-- Both original independent sign choices use exactly the
same certified prime group labels and true harmonic parameters.
Only Ptw may vary; the endpoint is STILL the original
SourceComparisonData record with unchanged non-prime fields. -/
theorem source_original_TRUE_source03_parity_real_fields434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) :
    SourceOriginalSource03CanonicalFieldsMatch434 z
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps) := by
  cases eps <;>
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The canonical original endpoint's Ptw support is EITHER
empty OR the entire REAL certified canonical group-prime union.
Both pass the original hParity subset constraint. -/
theorem source_original_TRUE_source03_parity_support434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) :
    (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps).Ptw =
      if eps then z.G else ∅ := by
  cases eps <;> rfl

/-- Disjointness among the actual ORIGINAL source03 S/Ts/Tb
fields, now PROVED for either constructed parity endpoint. -/
theorem source_original_TRUE_source03_parity_separation434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) :
    SourceOriginalSource03GroupSeparation434
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps) :=
  source_original_canonical_fields_original_group_separation434
    z _ (source_original_TRUE_source03_parity_real_fields434
      z u hL hd hcd eps)

/-- REAL source03 SMALL normalization V_g=sum_{p in group}1/p
and the actual Fock initial SMALL mass <=1 are automatic
for BOTH original endpoint sign choices, not new hypotheses. -/
theorem source_original_TRUE_source03_parity_initial_small_mass434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) (J ell : ℕ) :
    sourceOriginalActualSourceSignedInitialSmallMass434
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps) J ell ≤ 1 :=
  source_original_canonical_fields_true_initial_Fock_mass_le_one434
    z _ (source_original_TRUE_source03_parity_real_fields434
      z u hL hd hcd eps) J ell
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03CanonicalFourSigns -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 280000

/-- Independently changing the original allowed endpoint
parity choices does NOT alter its FULL unsigned arithmetic
coefficient core. The sole source of the parity change is
the true Ptw support of the existing original comparison data. -/
theorem source_original_TRUE_source03_two_signs_same_core434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps1 eps2 : Bool) :
    (sourceOriginalCanonicalComparisonParityChoice434
      z u hL hd hcd eps1).endpoint =
    (sourceOriginalCanonicalComparisonParityChoice434
      z u hL hd hcd eps2).endpoint := by
  cases eps1 <;> cases eps2 <;> rfl

/-- All FOUR INDEPENDENT sign combinations of the two original
source03 comparison endpoints have BOTH real prime-group field
normalizations, group uniqueness, canonical input mass <=1
and the exact endpoint Ptw supports. This is a concrete
mathematical interface only: it does NOT claim the correlation
saving for any of the four combinations. -/
theorem source_original_TRUE_source03_four_sign_comparison_data434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps1 eps2 : Bool) (J ell : ℕ) :
    let u1 := sourceOriginalCanonicalComparisonParityChoice434
      z u hL hd hcd eps1
    let u2 := sourceOriginalCanonicalComparisonParityChoice434
      z u hL hd hcd eps2
    SourceOriginalSource03CanonicalFieldsMatch434 z u1 ∧
    SourceOriginalSource03CanonicalFieldsMatch434 z u2 ∧
    u1.Ptw = (if eps1 then z.G else ∅) ∧
    u2.Ptw = (if eps2 then z.G else ∅) ∧
    u1.endpoint = u2.endpoint ∧
    sourceOriginalActualSourceSignedInitialSmallMass434 u1 J ell ≤ 1 ∧
    sourceOriginalActualSourceSignedInitialSmallMass434 u2 J ell ≤ 1 := by
  dsimp only
  exact ⟨source_original_TRUE_source03_parity_real_fields434
      z u hL hd hcd eps1,
    source_original_TRUE_source03_parity_real_fields434
      z u hL hd hcd eps2,
    source_original_TRUE_source03_parity_support434
      z u hL hd hcd eps1,
    source_original_TRUE_source03_parity_support434
      z u hL hd hcd eps2,
    source_original_TRUE_source03_two_signs_same_core434
      z u hL hd hcd eps1 eps2,
    source_original_TRUE_source03_parity_initial_small_mass434
      z u hL hd hcd eps1 J ell,
    source_original_TRUE_source03_parity_initial_small_mass434
      z u hL hd hcd eps2 J ell⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceNativeCanonicalSignBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The TWO canonical original SOURCE03 SourceComparisonData434 parity
branches do NOT use an arbitrary Ptw: each is the original full
true Ptw=z.G if epsilon=true, and Ptw=empty if false. Replacing
each branch by the SAME underlying unsigned endpoint with its
independent epsilon Bool and the true full z.G parity set is
literally coefficient-identical.

This closes the convention bridge between the original conditional
\`sourceOriginalCanonicalComparisonParityChoice434\` data constructor
and the four-channel \`sourceSignedCoefficients434 z.G eps\`, without
pretending that an arbitrary Ptw is a random subset or that its
signed raw harmonic expectation vanishes. -/
theorem source_native_original_CANONICAL_endpoint_sign_bridge434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps : Bool) (m : ℤ) :
    sourceSignedCoefficients434
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps).Ptw true
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps).endpoint m =
    sourceSignedCoefficients434 z.G eps
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd false).endpoint m := by
  have hCore := source_original_TRUE_source03_two_signs_same_core434
    z u hL hd hcd eps false
  have hParity := source_original_TRUE_source03_parity_support434
    z u hL hd hcd eps
  rw [hCore,hParity]
  cases eps <;> simp [sourceSignedCoefficients434,sourceEndpointSign434,
    literalSourceParity]

/-- Both independently selected ORIGINAL comparison endpoints
have their TRUE canonical parity branch exactly represented by
the fixed full z.G source four-sign coefficient functions.
The FULL joint kernel K remains unchanged; this is the missing
branch-by-branch SOURCE03 sign convention, not an analytic saving. -/
theorem source_native_original_CANONICAL_two_end_sign_bridge434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u v : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hL : 4 ≤ L) (hd : d<(1/2:ℝ)) (hcd : cfg.cexp<d)
    (eps1 eps2 : Bool) (m t : ℤ) :
    star (sourceSignedCoefficients434
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps1).Ptw true
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd eps1).endpoint m) *
    sourceSignedCoefficients434
      (sourceOriginalCanonicalComparisonParityChoice434
        z v hL hd hcd eps2).Ptw true
      (sourceOriginalCanonicalComparisonParityChoice434
        z v hL hd hcd eps2).endpoint t =
    star (sourceSignedCoefficients434 z.G eps1
      (sourceOriginalCanonicalComparisonParityChoice434
        z u hL hd hcd false).endpoint m) *
    sourceSignedCoefficients434 z.G eps2
      (sourceOriginalCanonicalComparisonParityChoice434
        z v hL hd hcd false).endpoint t := by
  rw [source_native_original_CANONICAL_endpoint_sign_bridge434
        z u hL hd hcd eps1 m,
    source_native_original_CANONICAL_endpoint_sign_bridge434
        z v hL hd hcd eps2 t]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeCanonicalFullTwistRAW -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The ORIGINAL SOURCE03 canonical FULL twist (Ptw=G) has a
deterministic source all-P J-history parity reference:
      (1-(-1)^(J0*|S/Ts/Tb groups|))/2.
The four canonical endpoint channel coefficients have been proved
equal to fixed z.G signed coefficients (not arbitrary-Ptw
surrogates). The full ORIGINAL J0-harmonic RAW scalar pairing
with true physical BIG auxiliary exclusion and no conditioned
law differs from this canonical reference by arbitrary L^-D
for any fixed J0 and mmax chosen before L.

The parity of J0*|G| may be EVEN, in which case the canonical
projected reference VANISHES. Hence this theorem does NOT
supply the required positive odd-prime mass; it identifies
precisely the remaining deterministic Fock/OLD phase and
signed comparison-integral obstruction. -/
theorem eventually_native_original_CANONICAL_FULL_TWIST_RAW434
    (r : ℕ) (hr : 1 ≤ r) (J0 mmax : ℕ) (Dsave : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (m : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J0 m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J0 m pat),
      m ≤ mmax →
      ∀ (w wp : ℕ),
      0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) → (wp:ℝ) ≤ Real.exp (2*L) →
      ∀ (A B : SourceNativeOriginalAllP434 r L → Finset ℕ),
      (∀ g, 0 < (A g).card) →
      (∀ g, 0 < (B g).card) →
      (∀ g, A g ⊆ w.primeFactors) →
      (∀ g, B g ⊆ wp.primeFactors) →
      ‖sourceNativeOriginalALLPJTrueProjectedRAW434
          r L J0 (sourceNativeOriginalG434 r L) A B -
        (1-(-1:ℂ)^(J0*Fintype.card
          (SourceNativeOriginalAllP434 r L)))/2‖ ≤
      L^(-Dsave) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_TRUE_PARITY_COMPARISON434
      r hr J0 mmax Dsave,
    eventually_source_native_CANONICAL_FULL_Ptw_ref434 r J0,
    eventually_native_original_ALL_P_masses434 r]
    with L hCompare hRef hMass
  refine ⟨hCompare.1, ?_⟩
  intro m pat aux hm w wp hw hwp hwCap hwpCap A B hA hB hAend hBend
  have hBound := hCompare.2 m pat aux hm w wp hw hwp hwCap hwpCap
    A B hA hB hAend hBend
    (sourceNativeOriginalG434 r L)
  have hExact := hRef.2
  have hV : ∀ g : SourceNativeOriginalAllP434 r L,
      0 < sourceNativeOriginalAllPMass434 r L g := by
    intro g
    exact ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive.trans_le
      (hMass g).1
  have hRefMean := source_native_original_ALL_P_J_true_four_sign_ref434
    r L J0 (sourceNativeOriginalG434 r L) hV
  rw [←hExact,hRefMean]
  exact hBound
end Green64Analytic.SourceBlockSieve

end

end

