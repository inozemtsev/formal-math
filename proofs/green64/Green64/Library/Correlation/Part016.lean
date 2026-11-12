module

public import Green64.Library.Correlation.Part015
public import Green64.Library.Weights.Part022
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part010

@[expose] public section

/-!
# Correlation / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualLiteralHistoryBaseRows -/

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- The totalized physical row sequence is real for i<N.
At i=N only its OLD-list field matters to the chronological rebase:
the OLD list is the genuine terminal Fock memory, not fabricated.
This dummy row is never used as a physical transition. -/
noncomputable def physicalActualLiteralHistoryBaseRows
    (hN : 0 < N) (i : ℕ) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  if hi : i < N then
    physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
  else
    { physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor 0 hN with
      pendingBefore := physicalActualLiteralPendingBefore
        SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig k N H N
      termIndices := ∅ }
/-- All actually visited rows retain the original full RowValid. -/
theorem physical_actual_literal_history_base_row_valid
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid
      (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN i) := by
  simp only [physicalActualLiteralHistoryBaseRows, dif_pos hi]
  exact physical_actual_literal_history_endpoint_row_valid
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hprime hnum i hi

/-- At every interior edge, including the edge entering the final
G_N vacuum visit, the actual source OLD list is a permutation
of precisely the next real OLD Fock list. -/
theorem physical_actual_literal_history_base_pending_step
    (hN : 0 < N) (i : ℕ) (hi : i < N) :
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).pendingNext.Perm
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN (i+1)).pendingBefore := by
  have hPrev :
      (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN i).pendingNext =
      physicalActualLiteralChronologicalNext SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
    simp only [physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  have hNext :
      (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN (i+1)).pendingBefore =
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H (i+1) := by
    by_cases hn : i+1 < N
    · simp only [physicalActualLiteralHistoryBaseRows, dif_pos hn]
      rfl
    · have heq : i+1=N := by omega
      simp only [physicalActualLiteralHistoryBaseRows, dif_neg hn]
      rw [heq]
  rw [hPrev, hNext]
  exact physical_actual_literal_interrow_pending_perm
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryCoherentRows -/

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
/-- Genuine physical rows with a coherent chronological OLD order.
Only Fin OLD term indices and promotion injections are rebased. -/
noncomputable def physicalActualLiteralHistoryCoherentRow
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  Green64Literal.coherentPendingRow N
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN)
    (fun j hj => physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum j hj)
    (physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN)
    i hi

theorem physical_actual_literal_history_coherent_row_valid
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid
      (physicalActualLiteralHistoryCoherentRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i hi) := by
  exact Green64Literal.coherent_pending_row_valid N
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN)
    (fun j hj => physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum j hj)
    (physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN)
    i hi
/-- The literal chronological pending equality is true LIST equality. -/
theorem physical_actual_literal_history_coherent_pending_link
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryCoherentRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).pendingNext =
    (physicalActualLiteralHistoryCoherentRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).pendingBefore := by
  rfl

/-- Order-normalized first-birth list. Its first element is
exactly the first true source active list; later elements preserve
the previous E-edge's original fresh TARGET list order. -/
noncomputable def physicalActualLiteralHistoryFresh
    (hN : 0 < N) : ℕ → List (PhysicalSourcePrime BP)
  | 0 =>
      (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN 0).active
  | i+1 =>
      (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN i).freshTarget

/-- Every fresh-list reorder preserves the exact FIRST-BIRTH SET. -/
theorem physical_actual_literal_history_fresh_support
    (hN : 0 < N) (i : ℕ) (hi : i < N) :
    (physicalActualLiteralHistoryFresh SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).toFinset =
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).freshBefore.toFinset := by
  cases i with
  | zero =>
      simp only [physicalActualLiteralHistoryFresh,
        physicalActualLiteralHistoryBaseRows, dif_pos hN]
      change (physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H 0).toFinset =
        (physicalActualLiteralFreshBefore SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H 0).toFinset
      exact (physical_actual_literal_initial_fresh_raw_support
        BP SP smallMod bigMod J ell m cap patterns
        q rho Vbig muBig k N H hN).symm
  | succ j =>
      have hj : j < N := by omega
      simp only [physicalActualLiteralHistoryFresh,
        physicalActualLiteralHistoryBaseRows, dif_pos hj, dif_pos hi]
      change (physicalActualLiteralFreshTarget SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H j).toFinset =
        (physicalActualLiteralFreshBefore SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H (j+1)).toFinset
      exact physical_actual_literal_interrow_fresh_support
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H j hj
/-- Single normalized original source RowValid, with genuine sigma/tau,
unmodified Fock weights, physical residues, chronological OLD indices,
and genuinely ordered interrow fresh lists. -/
noncomputable def physicalActualLiteralHistoryRow
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  Green64Literal.freshBeforeRebase
    (physicalActualLiteralHistoryCoherentRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi)
    (physicalActualLiteralHistoryFresh SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i)

theorem physical_actual_literal_history_row_valid
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    Green64Literal.RowValid
      (physicalActualLiteralHistoryRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i hi) := by
  apply Green64Literal.row_valid_fresh_before_rebase
    _ (physical_actual_literal_history_coherent_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum i hi) _
  change (physicalActualLiteralHistoryFresh SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).toFinset =
    (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).freshBefore.toFinset
  exact physical_actual_literal_history_fresh_support
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN i hi

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryOrderedLinks -/

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
variable (hN : 0 < N)
variable (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
variable (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
/-- All four original interrow equalities are exact LIST/Finset
equalities in the SINGLE rebased physical history. -/
theorem physical_actual_literal_history_ordered_active_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).nextActive =
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).active := by
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi, dif_pos hn]
  change (physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi).nextActive =
    (physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor (i+1) hn).active
  exact physical_actual_literal_history_endpoint_active_link
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi hn

theorem physical_actual_literal_history_ordered_pending_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).pendingNext =
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).pendingBefore := by
  exact physical_actual_literal_history_coherent_pending_link
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi hn

theorem physical_actual_literal_history_ordered_fresh_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).freshTarget =
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).freshBefore := by
  rfl
theorem physical_actual_literal_history_ordered_ever_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).everBornAfter =
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).everBornBefore := by
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi, dif_pos hn]
  change (physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i ∪
    (physicalActualLiteralFreshBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset) ∪
    (physicalActualLiteralGhostBatch SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).toFinset =
    physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H (i+1)
  exact physical_actual_literal_interrow_ever
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum i hi

theorem physical_actual_literal_history_ordered_offset_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N) :
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi).offsetAfter =
    (physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).offsetBefore := by
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi, dif_pos hn]
  rfl

theorem physical_actual_literal_history_ordered_residue_link
    (i : ℕ) (hi : i < N) (hn : i+1 < N)
    (p : PhysicalSourcePrime BP) :
    HEq
      ((physicalActualLiteralHistoryRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i hi).residueNext p)
      ((physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum (i+1) hn).residueBefore p) := by
  change HEq
    ((physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i).residueNext p)
    ((physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN (i+1)).residueBefore p)
  have hRowI : physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i =
      physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi := by
    simp only [physicalActualLiteralHistoryBaseRows, dif_pos hi]
  have hRowNext : physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN (i+1) =
      physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor (i+1) hn := by
    simp only [physicalActualLiteralHistoryBaseRows, dif_pos hn]
  rw [hRowI, hRowNext]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryComplete -/

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
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- Heterogeneous equality transports BOTH truly equal physical
residues across the original history's global-prime-value casts. -/
theorem physical_literal_cast_both_of_heq
    {A B C : Type} (e : A = C) (f : B = C)
    (a : A) (b : B) (h : HEq a b) :
    cast e a = cast f b := by
  cases e
  cases f
  exact eq_of_heq h

/-- Terminal specialization of the same fully proof-relevant cast. -/
theorem physical_literal_cast_one_of_heq
    {A C : Type} (e : A = C)
    (a : A) (b : C) (h : HEq a b) :
    cast e a = b := by
  cases e
  exact eq_of_heq h

/-- Total original history rows, with actual verified physical
normalization strictly inside the edge interval i<N. -/
noncomputable def physicalActualLiteralHistoryRows
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) :
    Green64Literal.SourceRow (P := PhysicalSourcePrime BP) BG
      (fun _ => J+ell) :=
  if hi : i < N then
    physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi
  else
    physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN i

/-- Unfold the whole dependent row before projecting residues or lists. -/
theorem physical_actual_literal_history_rows_at
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i =
    physicalActualLiteralHistoryRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i hi := by
  simp only [physicalActualLiteralHistoryRows, dif_pos hi]

theorem physical_actual_literal_history_rows_valid
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod)) :
    ∀ i, i < N →
      Green64Literal.RowValid
        (physicalActualLiteralHistoryRows SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          Vsmall Knu zeta theta anchor hN hprime hnum i) := by
  intro i hi
  simp only [physicalActualLiteralHistoryRows, dif_pos hi]
  exact physical_actual_literal_history_row_valid
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi

/-- Sum of exactly the source G_i eta coefficients on all E edges. -/
theorem physical_actual_literal_history_eta_sum
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod)) :
    (∑ i ∈ Finset.range N,
      (physicalActualLiteralHistoryRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i).eta) =
    ∑ i ∈ Finset.range N, sourceVisitEta q N i := by
  apply Finset.sum_congr rfl
  intro i hi
  have hlt : i < N := Finset.mem_range.mp hi
  simp only [physicalActualLiteralHistoryRows, dif_pos hlt,
    physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hlt]
  rfl
/-- Construct the FULL original LiteralHistory from the real G/E
physical path in the source root's vacuum sector.
The vacuum is an original root boundary, not part of an arbitrary
PhysicalFiniteActualWitnessPath. For N=0 use the separate G-only
boundary; the E-edge history here assumes N>0. -/
noncomputable def physicalActualLiteralHistory
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.LiteralHistory (P := PhysicalSourcePrime BP)
      (G := BG) (slots := fun _ => J+ell) N := by
  let B := physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  let F := physicalActualLiteralHistoryFresh SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  have hRAt (i : ℕ) (hi : i < N) :
      physicalActualLiteralHistoryRows SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i =
      physicalActualLiteralHistoryRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum i hi :=
    physical_actual_literal_history_rows_at
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum i hi
  have hBAt (i : ℕ) (hi : i < N) :
      B i =
      physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi := by
    simp only [B, physicalActualLiteralHistoryBaseRows, dif_pos hi]
  have hBValid : ∀ i, i < N → Green64Literal.RowValid (B i) := by
    intro i hi
    exact physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum i hi
  have hBStep : ∀ i, i < N →
      (B i).pendingNext.Perm (B (i+1)).pendingBefore := by
    intro i hi
    exact physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN i hi
  have hLast : N-1 < N := by omega
  have hFLast : F N = (B (N-1)).freshTarget := by
    have heq : (N-1)+1 = N := by omega
    rw [← heq]
    rfl
  have hBTerminal :
      (B N).pendingBefore =
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H N := by
    simp only [B, physicalActualLiteralHistoryBaseRows,
      dif_neg (Nat.lt_irrefl N)]
  have hTerminalPerm :
      (Green64Literal.coherentPending B N).Perm
      (physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H N) := by
    have h := Green64Literal.coherent_pending_perm N B hBValid
      hBStep N (Nat.le_refl N)
    rw [hBTerminal] at h
    exact h
  have hFinalFreshSubset :
      (F N).toFinset ⊆ (B (N-1)).nextActive.toFinset := by
    rw [hFLast, Green64Literal.row_target_support
      (B (N-1)) (hBValid (N-1) hLast)]
    exact Finset.subset_union_right
  have hFinalFreshNew :
      Disjoint (F N).toFinset (B (N-1)).everBornAfter := by
    rw [hFLast]
    exact (hBValid (N-1) hLast).next_fresh_unused
  refine {
    rows := physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum
    row_valid := physical_actual_literal_history_rows_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum
    finalActive := (B (N-1)).nextActive
    finalPending := Green64Literal.coherentPending B N
    finalFresh := F N
    finalEver := (B (N-1)).everBornAfter
    globalValue := physicalSourcePrimeValue BP bigMod
    globalLabelGroup := physicalSourcePrimeGroup BP
    globalGroupV := Vbig
    globalBaseline := fun p => physicalSourceBaseline BP bigMod q N p.1 p.2
    globalQ := q
    globalRho := rho
    rho_positive := hrho
    terminalEta := sourceVisitEta q N N
    terminal_eta_eq := ?_
    prime_global := ?_
    value_injective := hnum
    row_value_eq := ?_
    row_group_eq := ?_
    row_group_v_eq := ?_
    row_baseline_eq := ?_
    row_rho_eq := ?_
    row_q_eq := ?_
    row_eta_eq := ?_
    baseline_formula := ?_
    finalOffset := physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N
    finalResidues := physicalActualLiteralAnchoredResidue
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H anchor N (H.before N)
    final_pending_zero := ?_
    offset_link := ?_
    residue_link := ?_
    initial_offset := ?_
    initial_ever := ?_
    initial_pending := ?_
    initial_fresh := ?_
    final_fresh_subset := hFinalFreshSubset
    final_fresh_new := hFinalFreshNew
    links_active := ?_
    links_pending := ?_
    links_fresh := ?_
    links_ever := ?_
  }
  · simp [sourceVisitEta, sourceVisitQ]
  · intro p
    cases p with | mk g v => exact hprime g v
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    rfl
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    change (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).q =
      if i=0 then Real.sqrt q else q
    exact physical_actual_literal_history_scalar_row_q
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  · intro i hi
    simp only [physicalActualLiteralHistoryRows, dif_pos hi,
      physicalActualLiteralHistoryRow, Green64Literal.freshBeforeRebase,
      physicalActualLiteralHistoryCoherentRow,
      Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
      physicalActualLiteralHistoryBaseRows, dif_pos hi]
    change (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).eta =
      1 - (physicalActualLiteralHistoryScalarRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi).q
    exact physical_actual_literal_history_scalar_row_eta
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
  · intro p
    rw [physical_actual_literal_history_eta_sum
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum]
    exact physicalSourceBaseline_from_edge_visits BP bigMod
      q N p.1 p.2
  · intro p hp
    exact physical_actual_terminal_anchored_pending_zero
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H anchor hVac p
      (hTerminalPerm.mem_iff.mp hp)
  · intro i hi
    by_cases hn : i+1 < N
    · simpa only [if_pos hn, physicalActualLiteralHistoryRows,
        dif_pos hi, dif_pos hn] using
        (physical_actual_literal_history_ordered_offset_link
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi hn)
    · have heq : i+1 = N := by omega
      simp only [if_neg hn]
      rw [hRAt i hi]
      change (B i).offsetAfter =
        physicalActualOffset SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H N
      rw [hBAt i hi]
      change physicalActualOffset SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H (i+1) =
        physicalActualOffset SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H N
      rw [heq]
  · intro i hi p
    by_cases hn : i+1 < N
    · simp only [dif_pos hn]
      apply physical_literal_cast_both_of_heq
      rw [hRAt i hi, hRAt (i+1) hn]
      exact physical_actual_literal_history_ordered_residue_link
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
        hN hprime hnum i hi hn p
    · have heq : i+1 = N := by omega
      simp only [dif_neg hn]
      apply physical_literal_cast_one_of_heq
      have horig : HEq
          ((physicalActualLiteralHistoryRow SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H
            Vsmall Knu zeta theta anchor hN hprime hnum i hi).residueNext p)
          (physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H
            anchor (i+1) (H.before (i+1)) p) := by
        change HEq
          ((B i).residueNext p)
          (physicalActualLiteralAnchoredResidue SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H
            anchor (i+1) (H.before (i+1)) p)
        rw [hBAt i hi]
        rfl
      rw [heq] at horig
      rw [hRAt i hi]
      exact horig
  · simp only [if_pos hN]
    rw [hRAt 0 hN]
    change (B 0).offsetBefore = 0
    rw [hBAt 0 hN]
    change physicalActualOffset SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0 = 0
    simp [physicalActualOffset]
  · simp only [if_pos hN]
    rw [hRAt 0 hN]
    change (B 0).everBornBefore = ∅
    rw [hBAt 0 hN]
    change physicalActualLiteralEverBornBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0 = ∅
    exact physical_actual_literal_initial_ever_empty
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hnum
  · simp only [if_pos hN]
    rw [hRAt 0 hN]
    change (B 0).pendingBefore = []
    rw [hBAt 0 hN]
    change physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0 = []
    exact physical_actual_literal_initial_pending_nil
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H
  · simp only [if_pos hN]
    rw [hRAt 0 hN]
    change F 0 = (B 0).active
    rfl
  · intro i hi
    by_cases hn : i+1 < N
    · simpa only [if_pos hn, physicalActualLiteralHistoryRows,
        dif_pos hi, dif_pos hn] using
        (physical_actual_literal_history_ordered_active_link
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi hn)
    · have heq : i=N-1 := by omega
      simp only [if_neg hn, physicalActualLiteralHistoryRows,
        dif_pos hi]
      change (B i).nextActive = (B (N-1)).nextActive
      rw [heq]
  · intro i hi
    by_cases hn : i+1 < N
    · simpa only [if_pos hn, physicalActualLiteralHistoryRows,
        dif_pos hi, dif_pos hn] using
        (physical_actual_literal_history_ordered_pending_link
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi hn)
    · have heq : i+1=N := by omega
      simp only [if_neg hn, physicalActualLiteralHistoryRows,
        dif_pos hi]
      change Green64Literal.coherentPending B (i+1) =
        Green64Literal.coherentPending B N
      rw [heq]
  · intro i hi
    by_cases hn : i+1 < N
    · simp only [if_pos hn, physicalActualLiteralHistoryRows,
        dif_pos hi, dif_pos hn]
      change (B i).freshTarget = F (i+1)
      rfl
    · have heq : i+1=N := by omega
      simp only [if_neg hn, physicalActualLiteralHistoryRows,
        dif_pos hi]
      change (B i).freshTarget = F N
      rw [←heq]
      rfl
  · intro i hi
    by_cases hn : i+1 < N
    · simpa only [if_pos hn, physicalActualLiteralHistoryRows,
        dif_pos hi, dif_pos hn] using
        (physical_actual_literal_history_ordered_ever_link
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi hn)
    · have heq : i=N-1 := by omega
      simp only [if_neg hn, physicalActualLiteralHistoryRows,
        dif_pos hi]
      change (B i).everBornAfter = (B (N-1)).everBornAfter
      rw [heq]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryLifespanBridge -/

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
variable (k : ℤ) (N : ℕ)variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- The physical witness induces precisely one ORIGINAL compatible
lifespan profile. This is not yet a weighted G/E pushforward. -/
theorem physical_actual_literal_history_unique_profile
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    ∃! life : PhysicalSourcePrime BP → Option (ℕ × ℕ),
      Green64Literal.FitsHistory
        (physicalActualLiteralHistory SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac)
        life := by
  exact Green64Literal.literal_history_unique_profile _

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryWeightBridge -/

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
variable (k : ℤ) (N : ℕ)variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- The ORIGINAL global literal birth measure is the actual
physical mu-tilde with the source p*b_p normalization. -/
theorem physical_actual_literal_global_birth_mu
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (p : PhysicalSourcePrime BP) :
    Green64Literal.sourceGlobalMu
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) p =
    (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ) := by
  change (1:ℂ) / ((Vbig p.1:ℂ) * (bigMod p.1 p.2:ℂ) *
    (physicalSourceBaseline BP bigMod q N p.1 p.2:ℂ)) =
    (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ)
  exact (physicalMuTilde_cast_source BP bigMod q N Vbig p.1 p.2).symm
/-- All original physical source rows share precisely the true
mu-tilde birth density, including the baseline b_p. -/
theorem physical_actual_literal_row_birth_mu
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) (p : PhysicalSourcePrime BP) :
    Green64Literal.sourceMu
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i) p =
    (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ) := by
  exact (Green64Literal.sourceMu_eq_global _ i hi p).trans
    (physical_actual_literal_global_birth_mu
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum hrho hVac p)

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryInitialWeight -/

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
variable (k : ℤ) (N : ℕ)variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)
variable (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- Literal initial active list is the original ordered physical source list. -/
theorem physical_actual_literal_initial_active_list
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.visitActive
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) 0 =
      physicalActualLiteralRawSourceList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H 0 := by
  simp only [Green64Literal.visitActive, if_pos hN]
  change (physicalActualLiteralHistoryRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum 0).active =
    physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum 0 hN]
  change (physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN 0).active =
    physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0
  have hAt : physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN 0 =
    physicalActualLiteralHistoryEndpointRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor 0 hN := by
    simp [physicalActualLiteralHistoryBaseRows, dif_pos hN]
  rw [hAt]
  rfl

/-- The initial literal weighted birth product is exactly the
unsymmetrized physical G/E initial active mu-tilde product. -/
theorem physical_actual_literal_initial_birth_weight
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.literalInitialWeight
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) =
    ((physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0).map
      (fun p => (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ))).prod := by
  unfold Green64Literal.literalInitialWeight
  rw [physical_actual_literal_initial_active_list
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  exact physical_actual_literal_global_birth_mu
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac p
end Green64FullPhysicalE

end

