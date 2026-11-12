module

public import Green64.Library.Correlation.Part026
public import Green64.Library.Correlation.Part022
public import Green64.Library.Correlation.Part018
public import Green64.Library.Correlation.Part011
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part021
public import Green64.Library.Weights.Part024
public import Mathlib
public import Green64.Library.Weights.Part009
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Correlation / Part027

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryB2ImageFrozenWeightNonzero -/

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

set_option maxHeartbeats 700000

/-- Any ORIGINAL source frozen profile in the true forward image of
a contributing original indexed root has NONZERO original frozen
SMALL/Fourier path weight. Proof reads the actual path H from its
real nonzero source root, preserves the original Classical.choose
lifespan, and recovers the actual frozen omega equality. -/
theorem memory_source_actual_image_frozen_weight_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 ≠ 0 := by
  obtain ⟨xt,hp⟩ := himage
  by_cases hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m
      cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
  · let w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hw⟩
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd.R_pos hd.big_injective w)
    have hpf : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt =
        some (ω,fun gp : PhysicalSourcePrime BP => l gp.1 gp.2) := by
      unfold memorySourceRootFrozenProfile
      rw [dif_pos hw]
    have heq : (ω,fun gp : PhysicalSourcePrime BP => l gp.1 gp.2) = a :=
      Option.some.inj (hpf.symm.trans hp)
    have hω : ω = a.1 := congrArg Prod.fst heq
    have hW := memory_source_contributing_root_frozen_weight_nonzero
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R hd w
    rw [← hω]
    exact hW
  · have hh : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt = none := by
      unfold memorySourceRootFrozenProfile
      rw [dif_neg hw]
    rw [hh] at hp
    cases hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB2ImageRHSNonzero -/

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

/-- Every profile in the ACTUAL source forward image has a nonzero
unmodified frozen RHS. Its path weight is nonzero because each
true contributing root E witness carries the literal residual factor
and is itself nonzero. Its prime factors are nonzero by actual
finite-lifespan schedule support and source domain positivity.
Neither statement uses any global memory-fibre equality. -/
theorem memory_source_original_forward_image_rhs_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) ≠ 0 := by
  have hWeight :=
    memory_source_actual_image_frozen_weight_nonzero SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd a himage
  have hPrimeReal :=
    memory_source_actual_image_frozen_prime_product_ne_zero SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd a himage
  have hPrime : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) ≠ 0 := hPrimeReal
  exact mul_ne_zero hWeight (by exact_mod_cast hPrime)
end Green64FullPhysicalE

end

end

/-! ## MemoryB2ZeroImageClosed -/

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

/-- CLOSES THE EXACT ORIGINAL B2 DEBT without an additional zero-fibre
summing axiom: no zero-RHS source frozen profile can lie in the genuine
forward image of a nonzero-weight original physical root trace.
This is derived by true pointwise E/residual factorization and prime
lifespan positivity; NOT from the requested global memory-fibre target. -/
theorem memory_source_original_zero_image_debt_closed
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemorySourceZeroImageFibreDebt SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := by
  intro hd a hzero himage
  have hn := memory_source_original_forward_image_rhs_nonzero SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd a himage
  exact False.elim (hn hzero)
end Green64FullPhysicalE

end

end

/-! ## MemoryB2OriginalGlobalFibreClosed -/

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

/-- PROVED ORIGINAL UNMODIFIED MemoryGlobalActualFibreWeight.
For EVERY original frozen path/lifespan profile, including zero
source coefficients inside and outside image, the FULL weighted
finite sum of true original indexed root trace witnesses is exactly
the literal original frozen source coefficient and prime lifetime
product. Proof combines complete nonzero weighted-fibre result,
outside-image support zero, and actual nonzero-root source E
residual nonvanishing. No new hypotheses, replacement carriers,
global memory identity, or unproved zero-image assumption. -/
theorem memory_source_global_actual_fibre_weight_unconditional
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemoryGlobalActualFibreWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := by
  exact
    (memory_global_actual_fibre_weight_iff_zero_image_debt SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R).mpr
      (memory_source_original_zero_image_debt_closed SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R)
end Green64FullPhysicalE

end

end

/-! ## MemoryB3OriginalWeightedRootClosed -/

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

/-- ORIGINAL UNMODIFIED source global weighted root target.
The original exhaustive source physical G_0E_0...G_N indexed trace
sum equals the complete literal frozen omega/life sum, with
exact source OLD ghost, SMALL/Fourier kernel, reverse-K, V and
Fock orbit weights. This applies the proved physical root-fibre
disintegration and the original source fibre partition, and does
not assume any new fibre identity or root sampling distribution. -/
theorem memory_source_global_weighted_root_original_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemoryGlobalWeightedRootTarget SP smallMod BP bigMod
      J ell m patterns cap q rho Vsmall Vbig Knu zeta theta k R := by
  intro hd
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  have hparts := memory_source_full_root_frozen_fibre_partition SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd
  have hFibre := memory_source_global_actual_fibre_weight_unconditional SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R
  rw [hparts]
  unfold memoryFrozenSourceLifespanRoot
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro life hlife
  exact hFibre hd (ω,life)
end Green64FullPhysicalE

end

end

/-! ## MemoryB3OriginalPhysicalToHaar -/

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

/-- The ORIGINAL unmodified source physical Fock/Hilbert finite root
is exactly the original frozen-coordinate BIG Haar expectation root.
The proof composes three kernel-proven UNCONDITIONAL finite identities:
(1) exhaustive actual physical root -> original indexed root;
(2) original indexed root -> true omega/life weighted pushforward;
(3) true omega/life -> original frozen BIG Haar expectation.
Only the original domain is assumed, no stochastic exchange axiom,
root-degree quotient, root-fibre multiplicity or substituted measure.
The separate independent residue-row reindex remains open. -/
theorem memory_source_original_physical_root_eq_frozen_Haar
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap
      q rho Vsmall Vbig k R) :
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig Knu zeta theta k R =
    memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R := by
  calc
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
        q rho Vsmall Vbig Knu zeta theta k R =
      memorySourceFullRootIndexedSum SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R :=
          memory_source_finite_root_full_indexed_exact SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    _ = memoryFrozenSourceLifespanRoot SP smallMod BP bigMod
        J ell m patterns q Vsmall Vbig Knu zeta theta k R :=
          (memory_source_global_weighted_root_original_exact SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R) hd
    _ = memoryFrozenSourceHaarRoot SP smallMod BP bigMod
        J ell m patterns q Vsmall Vbig Knu zeta theta k R :=
          (memory_frozen_source_Haar_lifespan_exact SP smallMod BP bigMod
            J ell m patterns q Vsmall Vbig Knu zeta theta k R).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB3IdentityIndependentReduction -/

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

/-- The exact LAST FINITE source independent-side obligation.
Original unchanged MemoryIdentityTarget is equivalent, with NO extra
hypotheses, to equality of the original independent residue/Fourier
root with the explicit frozen source BIG-Haar expectation.
All physical Fock/G/E and frozen lifespan contributions are already
proved equal unconditionally in the original source domain.
This is an iff reduction, NOT a proof of the independent-side equality. -/
theorem memory_original_identity_iff_independent_frozen_Haar
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemoryIdentityTarget SP smallMod BP bigMod J ell m patterns cap
        q rho Vsmall Vbig Knu zeta theta k R ↔
    (∀ hd : MemorySourceDomain SP smallMod BP bigMod cap
        q rho Vsmall Vbig k R,
      memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k R =
      memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k R) := by
  constructor
  · intro hId hd
    calc
      memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k R =
        memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
          q rho Vsmall Vbig Knu zeta theta k R := hId hd
      _ = memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k R :=
            memory_source_original_physical_root_eq_frozen_Haar SP smallMod
              BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
              zeta theta k R hd
  · intro hInd hd
    calc
      memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k R =
        memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k R := hInd hd
      _ = memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
          q rho Vsmall Vbig Knu zeta theta k R :=
            (memory_source_original_physical_root_eq_frozen_Haar SP smallMod
              BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
              zeta theta k R hd).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalIdentityClosed -/

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

/-- The exact original independent root equals the complete frozen Haar root.
This is stronger than the source domain: only q >= 0 and R > 0 are needed. -/
theorem memory_independent_original_root_eq_frozen_Haar
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R) :
    memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R =
    memoryFrozenSourceHaarRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R := by
  rw [memory_independent_root_exact_full_array_sum]
  unfold memoryFrozenSourceHaarRoot
  cases hN : 2*R with
  | zero => omega
  | succ n =>
    exact memory_ind_original_full_sum_frozen_Haar SP smallMod BP bigMod
      J ell m patterns q hq Vsmall Vbig Knu zeta theta k n

/-- ORIGINAL MemoryIdentityTarget, under exactly the unchanged MemorySourceDomain.
No assumption of the independent/frozen bridge, kernel law, or source identity. -/
theorem memory_original_identity_target_proved
    (cap : BG → ℕ) (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemoryIdentityTarget SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig Knu zeta theta k R := by
  apply (memory_original_identity_iff_independent_frozen_Haar SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R).mpr
  intro hd
  exact memory_independent_original_root_eq_frozen_Haar SP smallMod BP bigMod
    J ell m patterns q hd.q_pos.le Vsmall Vbig Knu zeta theta k R hd.R_pos
end Green64FullPhysicalE

end

end

/-! ## SourceNativeFullPhysicalSmallMarkD -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- LITERAL original full physical SOURCE03 D for J=1,ell=0:
EVERY original SMALL S/Ts group contributes its single
Haar zero-marked active prime to the real source divisor D,
regardless of BIG auxiliary free counts, BIG labels and OLD state.

The source small mark is selected via the ORIGINAL
\`sourceSmallShared 1 0\`, not inserted as an assumed prime
factor of D. This exact divisibility is the arithmetic reason
the source translated SMALL Haar target can preserve its own
zero-marked prime when the common source step is 2kD. -/
theorem source_original_J1_FULL_physical_SMALL_mark_dvd_D434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type)
    [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ)
    [∀ g, ∀ p, NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (bigMod g p)]
    (m : ℕ) (cap : BG → ℕ)
    (pat : SourcePattern BG 1 m)
    (aux : SourceBigAux BP 1 m pat)
    (x : FullPhysicalState SP smallMod BP bigMod 1 cap)
    (g : SG) :
    smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)) ∣
      sourcePhysicalD SP smallMod BP bigMod
        1 0 m cap pat aux x := by
  classical
  let smallFactor : SG → ℕ := fun gg =>
    ∏ i ∈ sourceSmallShared 1 0 gg,
      smallMod gg (marks (smallMod gg) 1 (x.1 gg) i)
  have hSlot : (0:Fin 1) ∈ sourceSmallShared 1 0 g := by
    simp [sourceSmallShared]
  have hLocal :
      smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)) ∣
        smallFactor g :=
    Finset.dvd_prod_of_mem
      (fun i : Fin 1 =>
        smallMod g (marks (smallMod g) 1 (x.1 g) i)) hSlot
  have hGlobal : smallFactor g ∣ ∏ gg : SG, smallFactor gg :=
    Finset.dvd_prod_of_mem smallFactor (Finset.mem_univ g)
  have hSmall := hLocal.trans hGlobal
  change smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)) ∣
    (∏ gg : SG, smallFactor gg) *
    (∏ gg : BG,
      (∏ i ∈ sourceBigShared 1 0 m pat gg,
        bigMod gg ((x.2 gg).1 i)) *
      (∏ j : ↥(pat.free gg), bigMod gg (aux gg j)))
  exact dvd_mul_of_dvd_left hSmall _

/-- Consequently the ORIGINAL integer signed physical source
step orientation*k*D vanishes modulo each zero-marked
SMALL S/Ts prime, for arbitrary original BIG free auxiliary
patterns and arbitrary nonzero k. It is not an assumption
that all small torus coordinates are fixed: only ACTUALLY
SHARED zero-marked prime coordinates are fixed. -/
theorem source_original_J1_SMALL_mark_dvd_signed_step434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type)
    [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ)
    [∀ g, ∀ p, NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (bigMod g p)]
    (m : ℕ) (cap : BG → ℕ)
    (pat : SourcePattern BG 1 m)
    (aux : SourceBigAux BP 1 m pat)
    (x : FullPhysicalState SP smallMod BP bigMod 1 cap)
    (orientation k : ℤ) (g : SG) :
    (smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)) : ℤ) ∣
      sourcePhysicalStep SP smallMod BP bigMod
        1 0 m cap pat aux x orientation k := by
  have hd := source_original_J1_FULL_physical_SMALL_mark_dvd_D434
    SP smallMod BP bigMod m cap pat aux x g
  have hdint : (smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)):ℤ) ∣
      (sourcePhysicalD SP smallMod BP bigMod
        1 0 m cap pat aux x:ℤ) := by
    exact_mod_cast hd
  unfold sourcePhysicalStep
  exact dvd_mul_of_dvd_right hdint (orientation*k)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeFullPhysicalSMALLTarget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The ORIGINAL physical source SMALL Haar torus target
EXISTS and is genuinely allowed at the signed physical
displacement orientation*k*D for EVERY actual source full
Fock state with J=1 and any BIG free pattern.

It is NOT correct to set the entire target SMALL torus equal
to source: most UNMARKED small-prime coordinates are shifted
by the same signed step and need not divide D. The correct
target is the full translated torus y'_g=y_g+step mod p
for EVERY coordinate, with the original shared mark p_g
retained at zero because p_g|D (proved from the real source
small shared factor). Source and target mark lists are exact
Fin 1 ordered labels; both original permutation families
are identity.

This theorem rules out a hidden zero from the SMALL
support indicator for the constructed real physical
J=1,m=1 branch, without introducing a fictitious fixed torus
or prematurely claiming any bound on the complex Fourier K. -/
theorem source_original_FULL_PHYSICAL_J1_SMALL_Haar_target434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type)
    [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ)
    [∀ g, ∀ p, NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (bigMod g p)]
    (m : ℕ) (cap : BG → ℕ)
    (pat : SourcePattern BG 1 m)
    (aux : SourceBigAux BP 1 m pat)
    (x : FullPhysicalState SP smallMod BP bigMod 1 cap)
    (orientation k : ℤ) :
    let step := sourcePhysicalStep SP smallMod BP bigMod
       1 0 m cap pat aux x orientation k;
    ∃ z : GroupState SP smallMod 1,
      groupEdgeAllowedPerm SP smallMod 1
        (sourceSmallShared 1 0) step
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
        x.1 z := by
  classical
  let step := sourcePhysicalStep SP smallMod BP bigMod
      1 0 m cap pat aux x orientation k
  have hstep (g : SG) :
      (smallMod g (marks (smallMod g) 1 (x.1 g) (0:Fin 1)):ℤ) ∣ step :=
    source_original_J1_SMALL_mark_dvd_signed_step434
      SP smallMod BP bigMod m cap pat aux x orientation k g
  have hzero (g : SG) :
      (step : ZMod (smallMod g (marks (smallMod g) 1
        (x.1 g) (0:Fin 1)))) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd step
      (smallMod g (marks (smallMod g) 1 (x.1 g) 0))).mpr
      (hstep g)
  let z : GroupState SP smallMod 1 := fun g =>
    ⟨((translate (smallMod g) step
        (residues (smallMod g) 1 (x.1 g))),
      (marks (smallMod g) 1 (x.1 g))), by
      constructor
      · exact marks_injective (smallMod g) 1 (x.1 g)
      · intro i
        have heq : i = (0:Fin 1) := Subsingleton.elim _ _
        subst i
        change residues (smallMod g) 1 (x.1 g)
          (marks (smallMod g) 1 (x.1 g) 0) +
          (step : ZMod (smallMod g
            (marks (smallMod g) 1 (x.1 g) 0))) = 0
        rw [marked_zero (smallMod g) 1 (x.1 g) 0, hzero g]
        simp⟩
  refine ⟨z,?_⟩
  intro g
  change edgeAllowedPerm (smallMod g) 1
    (sourceSmallShared 1 0 g) step
    (Equiv.refl _) (Equiv.refl _) (x.1 g) (z g)
  constructor
  · rfl
  · intro i hi
    rfl
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalMemoryOldEndpointSandwich -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The genuine OLD damping at the actual ordered source Fock state.
It depends on that endpoint only, not on Nu, auxiliary marks,
permutations, store/promote witnesses or the complex Knu. -/
noncomputable def sourceOriginalMemoryOldInput434
    (rho : ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) : ℂ :=
  ∏ g : BG, (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount ((x.2 g).2)

/-- The genuine OLD damping at the actual symmetric target Fock state.
All equal prime/residue occurrences are counted with multiplicity. -/
noncomputable def sourceOriginalMemoryOldOutput434
    (rho : ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℂ :=
  ∏ g : BG, (rho : ℂ) ^ ((y.2 g).2.countP (fun a => a.2 = 0))

/-- Exact OLD factorization for ONE original physical source choice.
The formula includes dirty store/promote choices, all source legality
constraints and the same original moving D, Knu and independent
permutations. No ideal law or smallness hypothesis is introduced. -/
theorem source_original_memory_OLD_source_coefficient_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vs Vb mu K zeta theta o k x z =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q 1 Vs Vb mu K zeta theta o k x z *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho
        (sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns x o k z) := by
  classical
  let b := z.2.2.1
  let step := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1 o k
  have hGroup (g : BG) :
      orientedBigBranchCoefficient (bigMod g) (J+ell) (cap g)
        (mu g) (Vb g) rho (x.2 g) (b.bigChoice g).1
        (sourceBigShared J ell m (patterns z.1) g)
        (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2 =
      (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount ((x.2 g).2) *
        orientedBigBranchCoefficient (bigMod g) (J+ell) (cap g)
          (mu g) (Vb g) 1 (x.2 g) (b.bigChoice g).1
          (sourceBigShared J ell m (patterns z.1) g)
          (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2 *
        (rho : ℂ) ^ outputZeroCount (bigMod g) (J+ell) (cap g)
          (x.2 g) (b.sigmaBig g) step (b.bigChoice g).2 := by
    simp only [orientedBigBranchCoefficient, Complex.ofReal_one,
      one_pow, one_mul, pow_add]
    ring
  have hProduct :
      (∏ g : BG, orientedBigBranchCoefficient
        (bigMod g) (J+ell) (cap g) (mu g) (Vb g) rho
        (x.2 g) (b.bigChoice g).1
        (sourceBigShared J ell m (patterns z.1) g)
        (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) =
      sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      (∏ g : BG, orientedBigBranchCoefficient
        (bigMod g) (J+ell) (cap g) (mu g) (Vb g) 1
        (x.2 g) (b.bigChoice g).1
        (sourceBigShared J ell m (patterns z.1) g)
        (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho
        (sourceOrientedPhysicalOutput SP smallMod BP bigMod
          J ell m cap patterns x o k z) := by
    simp_rw [hGroup]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rfl
  unfold sourceOrientedPhysicalCoefficient
  dsimp only
  change _ = _
  rw [show (∏ g : BG, orientedBigBranchCoefficient
      (bigMod g) (J+ell) (cap g) (mu g) (Vb g) rho
      (x.2 g) (b.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) = _ from hProduct]
  ring

/-- Exact coherent ORIGINAL E kernel identity. All histories with the
same physical endpoints share these two OLD factors, so no termwise
absolute value or arbitrary history-dependent damping is substituted. -/
theorem source_original_memory_OLD_kernel_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k x y *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y := by
  classical
  unfold orientedEdgeStateKernel
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x o k z = y
  · simp only [if_pos h]
    rw [source_original_memory_OLD_source_coefficient_sandwich434
      SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
      K zeta theta o k x z, h]
  · simp only [if_neg h, mul_zero, zero_mul]

/-- The same exact factorization for the entire original physical
operator applied to an arbitrary target observable, including Fock
observables. The rho=1 kernel is a reference identity, not a claimed
small operator or an alteration of the original evolution. -/
theorem source_original_memory_OLD_operator_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x F =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      fullSourceOrientedPhysicalE SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k x
        (fun y => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho y * F y) := by
  classical
  unfold fullSourceOrientedPhysicalE
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [source_original_memory_OLD_source_coefficient_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
    K zeta theta o k x z]
  ring


/-- The OLD endpoint identity holds for the genuine ORIGINAL CLEAN
kernel itself, with its literal no-store/no-promotion predicate. -/
theorem source_original_memory_OLD_clean_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    memoryOriginalCleanEdgeKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      memoryOriginalCleanEdgeKernel SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k x y *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y := by
  classical
  unfold memoryOriginalCleanEdgeKernel
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x o k z = y ∧
      memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z
  · simp only [if_pos h]
    rw [source_original_memory_OLD_source_coefficient_sandwich434
      SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu
      K zeta theta o k x z, h.1]
  · simp only [if_neg h, mul_zero, zero_mul]

/-- The actual signed E-minus-CLEAN remainder transforms by the SAME
physical endpoint factors. The middle difference is the original
rho=1 DIRTY kernel, not an artificially centered substitute. -/
theorem source_original_memory_OLD_signed_remainder_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y -
    memoryOriginalCleanEdgeKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y =
    sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x *
      memoryOriginalDirtyEdgeKernel SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k x y *
      sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y := by
  rw [source_original_memory_OLD_kernel_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu K zeta theta o k x y,
    source_original_memory_OLD_clean_sandwich434
    SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu K zeta theta o k x y,
    memory_original_E_clean_dirty_partition SP smallMod BP bigMod
      J ell m cap patterns q 1 Vs Vb mu K zeta theta o k x y]
  ring

/-- Actual OLD endpoint factors are contractions when 0≤ rho≤1;
this alone makes no claim of smallness for the full Memory chain. -/
theorem source_original_memory_OLD_input_norm_le_one434
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    ‖sourceOriginalMemoryOldInput434 SP smallMod BP bigMod J ell cap rho x‖ ≤ 1 := by
  simp only [sourceOriginalMemoryOldInput434, norm_prod, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  apply Finset.prod_le_one₀
  · intro g hg
    positivity
  · intro g hg
    exact pow_le_one₀ h0 h1

theorem source_original_memory_OLD_output_norm_le_one434
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    ‖sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y‖ ≤ 1 := by
  simp only [sourceOriginalMemoryOldOutput434, norm_prod, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  apply Finset.prod_le_one₀
  · intro g hg
    positivity
  · intro g hg
    exact pow_le_one₀ h0 h1
end Green64FullPhysicalE

end

