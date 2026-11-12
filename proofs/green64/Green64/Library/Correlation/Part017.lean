module

public import Green64.Library.Correlation.PhysicalActualLiteralGhostBirthWeight
public import Green64.Library.Correlation.Part016
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part014
public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part015
public import Green64.Library.Correlation.Part006
public import Green64.Library.Correlation.Part007
public import Green64.Library.Correlation.Part009

@[expose] public section

/-!
# Correlation / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualLiteralGhostBirthHistory -/

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
variable (Vsmall : SG → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ)
variable (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))

/-- The chronologically coherent literal source row retains exactly
the original physical G ghost batch, including ordered repetitions. -/
theorem physical_actual_literal_history_ghost_batch
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    ((physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i).ghostBatch =
      physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i := by
  change (physicalActualLiteralHistoryRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i).ghostBatch = _
  rw [physical_actual_literal_history_rows_at SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  rfl
/-- The true G ghost-birth branch masses are the literal row
birth masses, provided the physical witness uses source mu-tilde.
Neither numerical prime distinctness nor ordering is discarded. -/
theorem physical_actual_literal_ghost_birth_history_weight
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) (hi : i < N) :
    let Hlit := physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac
    ((Hlit.rows i).ghostBatch.map (Green64Literal.sourceMu (Hlit.rows i))).prod =
      ∏ g : BG, ∏ j : Fin ((H.ghost i g).2.1.val),
        (muBig g ((H.ghost i g).2.2 j).1 : ℂ) := by
  dsimp only
  let Hlit := physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac
  change ((Hlit.rows i).ghostBatch.map
    (Green64Literal.sourceMu (Hlit.rows i))).prod = _
  calc
    _ = ((Hlit.rows i).ghostBatch.map (fun p =>
        (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro p hp
      exact physical_actual_literal_row_birth_mu
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
        hN hprime hnum hrho hVac i hi p
    _ = ((physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).map
        (fun p => (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ))).prod := by
      rw [physical_actual_literal_history_ghost_batch
        SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
        k N H Vsmall Knu zeta theta anchor
        hN hprime hnum hrho hVac i hi]
    _ = _ := physical_actual_ghost_group_birth_muBig
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hmu i
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralGhostGroupMass -/

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

/-- The actual groupwise ordered G birth list is a field of the
original chronologically coherent LiteralHistory, without quotienting. -/
theorem physical_actual_literal_history_ghost_group
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) (g : BG) :
    ((physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i).ghostBatches g =
      physicalActualLiteralGhostGroup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i g := by
  change (physicalActualLiteralHistoryRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i).ghostBatches g = _
  rw [physical_actual_literal_history_rows_at SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  rfl
/-- The exact original G group batch cardinal equals the literal
ghostWeight factorial exponent at EVERY physical history row. -/
theorem physical_actual_literal_history_batchSize
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) (g : BG) :
    Green64Literal.batchSize
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
        zeta theta anchor hN hprime hnum hrho hVac).rows i) g =
      (H.ghost i g).2.1.val := by
  let Hlit := physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
    zeta theta anchor hN hprime hnum hrho hVac
  change Green64Literal.batchSize (Hlit.rows i) g = _
  rw [Green64MemoryGhostOp.literal_batchSize_eq_group_batch_length
    (Hlit.rows i) (Hlit.row_valid i hi) g]
  rw [physical_actual_literal_history_ghost_group
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi g]
  simp [physicalActualLiteralGhostGroup]
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralGhostBirthCoefficient -/

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
/-- Exact q_i, eta_i, rho and V_g of the literal source ghost row
after both chronological OLD and first-birth display reindexing. -/
theorem physical_actual_literal_ghost_row_scalar_fields
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i
    f.eta = sourceVisitEta q N i ∧
    f.rho = rho ∧ f.groupV = Vbig := by
  dsimp only
  change
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).eta = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).rho = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).groupV = _
  rw [physical_actual_literal_history_rows_at SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow, Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow, physicalActualLiteralHistoryScalarRow]
  exact ⟨rfl, rfl, rfl⟩
/-- The entire G ghost-BIRTH multiplier: exactly ONE b_g! per
group, the original -eta_i V_g/rho coefficient, and the true mu-tilde
birth measure. This is only the birth part of ghostWeight: old-zero
and termination factors are not dropped or claimed proved here. -/
theorem physical_actual_literal_ghost_group_birth_coeff
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i
    (∏ g : BG,
       ((1:ℂ) / (Nat.factorial (Green64Literal.batchSize f g):ℂ)) *
       ((-(f.eta:ℂ) * (f.groupV g:ℂ) / (f.rho:ℂ)) ^
        Green64Literal.batchSize f g)) *
      (f.ghostBatch.map (Green64Literal.sourceMu f)).prod =
    (∏ g : BG,
       ((1:ℂ) / (Nat.factorial ((H.ghost i g).2.1.val):ℂ)) *
       ((-(sourceVisitEta q N i:ℂ) * (Vbig g:ℂ) / (rho:ℂ)) ^
         (H.ghost i g).2.1.val)) *
      (∏ g : BG, ∏ j : Fin ((H.ghost i g).2.1.val),
        (muBig g ((H.ghost i g).2.2 j).1 : ℂ)) := by
  dsimp only
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  change (∏ g : BG, _ * _) * (f.ghostBatch.map (Green64Literal.sourceMu f)).prod = _
  have hFields := physical_actual_literal_ghost_row_scalar_fields
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
    k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi
  dsimp only at hFields
  obtain ⟨hEta, hRho, hV⟩ := hFields
  have hBirth := physical_actual_literal_ghost_birth_history_weight
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
    k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac hmu i hi
  dsimp only at hBirth
  rw [hBirth]
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  rw [physical_actual_literal_history_batchSize
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
    k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi g, hEta, hRho, hV]
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryTerminalWeight -/

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

/-- At terminal G_N the coherent OLD ordering preserves the
original Fock multiplicity exactly, not merely its support. -/
theorem physical_actual_literal_final_pending_perm
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).finalPending.Perm
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N) := by
  let B := physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  have hValid : ∀ i, i < N → Green64Literal.RowValid (B i) := by
    intro i hi
    exact physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum i hi
  have hStep : ∀ i, i < N →
      (B i).pendingNext.Perm (B (i+1)).pendingBefore := by
    intro i hi
    exact physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN i hi
  change (Green64Literal.coherentPending B N).Perm
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N)
  have h := Green64Literal.coherent_pending_perm N B
    hValid hStep N (Nat.le_refl N)
  have hTerminal : (B N).pendingBefore =
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H N := by
    simp only [B, physicalActualLiteralHistoryBaseRows,
      dif_neg (Nat.lt_irrefl N)]
  rw [hTerminal] at h
  exact h

/-- The terminal literal weight is the physical G_N coefficient
with the genuine incoming Fock OLD-list multiplicity. -/
theorem physical_actual_literal_terminal_factor_flat
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.literalTerminalWeight
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) =
    ((-(sourceVisitEta q N N : ℝ)) / rho : ℂ) ^
      (physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H N).length := by
  unfold Green64Literal.literalTerminalWeight
  have hEta :
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).terminalEta =
      sourceVisitEta q N N := by rfl
  have hRho :
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).globalRho =
      rho := by rfl
  rw [hEta, hRho]
  rw [(physical_actual_literal_final_pending_perm
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac).length_eq]
  push_cast
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryTerminalGroupWeight -/

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

/-- Real terminal OLD-list length, including group and Fock multiplicity. -/
theorem physical_actual_literal_terminal_group_length :
    (physicalActualLiteralPendingBefore SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H N).length =
    ∑ g : BG, (Green64Fock.fockToList (((H.before N).2 g).2)).length := by
  simp [physicalActualLiteralPendingBefore, List.length_flatMap]

/-- Exact terminal source G_N factor in genuine grouped Fock form:
the rebase of OLD indices never changes multiplicity coefficients. -/
theorem physical_actual_literal_terminal_factor_groups
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.literalTerminalWeight
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) =
    ∏ g : BG, ((-(sourceVisitEta q N N : ℝ)) / rho : ℂ) ^
      (Green64Fock.fockToList (((H.before N).2 g).2)).length := by
  rw [physical_actual_literal_terminal_factor_flat
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac,
    physical_actual_literal_terminal_group_length
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H]
  exact (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset BG)
    (fun g => (Green64Fock.fockToList (((H.before N).2 g).2)).length)
    ((-(sourceVisitEta q N N : ℝ)) / rho : ℂ)).symm

/-- The original literal terminal coefficient matches the
actual terminal G_N witness scalar, not merely an invented weight. -/
theorem physical_actual_literal_terminal_eq_real_G
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.literalTerminalWeight
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) =
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N N Vbig muBig
      (H.before N) (H.afterG N) (H.ghost N) := by
  rw [physical_actual_literal_terminal_factor_groups
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac,
    physical_actual_terminal_G_vacuum_coefficient
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H hVac]
end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryPhaseWeight -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Literal spectral/Fourier edge scalar equals the actual source
oriented coefficient, with no synthetic phase or modified divisor. -/
theorem source_original_scalar_is_literal_phase
    {P G : Type} [DecidableEq P] [Fintype G]
    {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots) :
    Green64Literal.orientedKernel f * Green64Literal.additivePhase f =
      originalEdgeScalar f.kernelK f.zeta f.theta
        f.divisorD f.orientation f.k := by
  unfold Green64Literal.orientedKernel
    Green64Literal.additivePhase originalEdgeScalar
    originalOrientedKernel originalReturnPhase
  simp only [Int.cast_mul, Int.cast_natCast]
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralHistoryPathWeight -/

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

/-- Exact endpoint-matched literal path weight for the original
physical witness. The only remaining factors are the actual
literal row weights, still requiring comparison with physical E. -/
theorem physical_actual_literal_path_weight_endpoint_reduction
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    Green64Literal.literalPathWeight
      (physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac) =
    ((physicalActualLiteralRawSourceList SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H 0).map
      (fun p => (physicalSourceMuTilde BP bigMod q N Vbig p.1 p.2 : ℂ))).prod *
    (∏ i ∈ Finset.range N, Green64Literal.literalRowWeight
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i)) *
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N N Vbig muBig
      (H.before N) (H.afterG N) (H.ghost N) := by
  unfold Green64Literal.literalPathWeight
  rw [physical_actual_literal_initial_birth_weight
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac,
    physical_actual_literal_terminal_eq_real_G
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum hrho hVac]

end Green64FullPhysicalE

end

/-! ## PhysicalActualLiteralWeightRebase -/

section

open Classical
open scoped BigOperators

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Reordering only endpoint-active lists does not alter the original
row coefficient; sigma/tau and OLD indices remain untouched. -/
theorem literal_row_weight_endpoint_active
    (f : SourceRow (P := P) G slots) :
    literalRowWeight (endpointActiveRow f) = literalRowWeight f := rfl

/-- Reordering the first-birth display list leaves all source
coefficient fields exactly unchanged. -/
theorem literal_row_weight_fresh_before
    (f : SourceRow (P := P) G slots) (xs : List P) :
    literalRowWeight (freshBeforeRebase f xs) =
      literalRowWeight f := rfl

/-- Termination index cardinal equals the number of ended
prime labels, using the genuine OLD list's Nodup invariant. -/
theorem literal_term_indices_card_eq_ended
    (f : SourceRow (P := P) G slots) (h : RowValid f) :
    f.termIndices.card = (ended f).card := by
  unfold ended
  exact (Finset.card_image_of_injective _
    (List.nodup_iff_injective_get.mp h.pending_nodup)).symm

/-- Rebased OLD termination positions retain their full multiplicity
count, without substituting source OLD promotion indices. -/
theorem literal_term_count_pending_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (pendingRebaseRow f h xs hp).termIndices.card =
      f.termIndices.card := by
  calc
    _ = (ended (pendingRebaseRow f h xs hp)).card :=
      literal_term_indices_card_eq_ended _
        (row_valid_pending_rebase f h xs hp)
    _ = (ended f).card := by
      rw [pending_rebase_ended f h xs hp]
    _ = f.termIndices.card :=
      (literal_term_indices_card_eq_ended f h).symm

/-- An ordered Nodup list and its actual Fin indices count any
residue predicate identically. This is not a Finset approximation
to the list; it is a bijection of occurrence indices. -/
theorem literal_nodup_index_filter_card
    (xs : List P) (hxs : xs.Nodup) (z : P → Prop)
    [DecidablePred z] :
    ((Finset.univ : Finset (Fin xs.length)).filter
      (fun j => z (xs.get j))).card =
      (xs.toFinset.filter z).card := by
  have hinj : Function.Injective xs.get :=
    List.nodup_iff_injective_get.mp hxs
  have hImage :
      ((Finset.univ : Finset (Fin xs.length)).filter
        (fun j => z (xs.get j))).image xs.get =
      xs.toFinset.filter z := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, List.mem_toFinset]
    constructor
    · rintro ⟨j, hz, rfl⟩
      exact ⟨List.get_mem _ _, hz⟩
    · rintro ⟨hp, hz⟩
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
      exact ⟨j, hj ▸ hz, hj⟩
  rw [← hImage]
  exact (Finset.card_image_of_injective _ hinj).symm

/-- A genuine permutation of a Nodup OLD list preserves every
index-predicate count, including all zero-residue tests. -/
theorem literal_perm_index_filter_card
    (xs ys : List P) (hp : xs.Perm ys) (z : P → Prop)
    [DecidablePred z] (hy : ys.Nodup) :
    ((Finset.univ : Finset (Fin xs.length)).filter
      (fun j => z (xs.get j))).card =
    ((Finset.univ : Finset (Fin ys.length)).filter
      (fun j => z (ys.get j))).card := by
  rw [literal_nodup_index_filter_card xs
    (hp.nodup_iff.mpr hy) z,
    literal_nodup_index_filter_card ys hy z]
  congr 1
  ext p
  simp only [Finset.mem_filter, List.mem_toFinset]
  exact and_congr hp.mem_iff Iff.rfl

/-- Rebased OLD enumeration has the same zero-residue count. -/
theorem literal_old_zero_count_pending_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (oldZeroIndices (pendingRebaseRow f h xs hp)).card =
      (oldZeroIndices f).card := by
  change ((Finset.univ : Finset (Fin xs.length)).filter
      (fun j => f.residueBefore (xs.get j) = 0)).card =
    ((Finset.univ : Finset (Fin f.pendingBefore.length)).filter
      (fun j => f.residueBefore (f.pendingBefore.get j) = 0)).card
  exact literal_perm_index_filter_card xs f.pendingBefore hp
    (fun p => f.residueBefore p = 0) h.pending_nodup

/-- G-output OLD zero tests are invariant under true pending
permutation, counting indices and not just the distinct labels. -/
theorem literal_visit_zero_count_pending_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (visitZeroIndices (pendingRebaseRow f h xs hp)).card =
      (visitZeroIndices f).card := by
  change ((Finset.univ : Finset (Fin (pendingAfterRebase f xs).length)).filter
      (fun j => f.residueAfter ((pendingAfterRebase f xs).get j) = 0)).card =
    ((Finset.univ : Finset (Fin f.pendingAfter.length)).filter
      (fun j => f.residueAfter (f.pendingAfter.get j) = 0)).card
  exact literal_perm_index_filter_card
    (pendingAfterRebase f xs) f.pendingAfter
    (pending_after_rebase_perm f h xs hp)
    (fun p => f.residueAfter p = 0) h.pendingAfter_nodup

/-- E-output zero-residue tests also retain their exact
multiplicities under the coherent OLD enumeration. -/
theorem literal_target_zero_count_pending_rebase
    (f : SourceRow (P := P) G slots) (h : RowValid f)
    (xs : List P) (hp : xs.Perm f.pendingBefore) :
    (targetZeroIndices (pendingRebaseRow f h xs hp)).card =
      (targetZeroIndices f).card := by
  change ((Finset.univ : Finset (Fin (pendingNextRebase f xs).length)).filter
      (fun j => f.residueNext ((pendingNextRebase f xs).get j) = 0)).card =
    ((Finset.univ : Finset (Fin f.pendingNext.length)).filter
      (fun j => f.residueNext (f.pendingNext.get j) = 0)).card
  exact literal_perm_index_filter_card
    (pendingNextRebase f xs) f.pendingNext
    (pending_next_rebase_perm f h xs hp)
    (fun p => f.residueNext p = 0) h.pendingNext_nodup

end Green64Literal

end

/-! ## PhysicalGhostOldOccurrenceCount -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Index count, with repetitions, of a predicate on an ordered OLD list.
The Fin-index description is primary; no prime-set quotient is taken. -/
theorem physical_old_index_card_eq_countP
    {U : Type} (xs : List U) (z : U → Prop) [DecidablePred z] :
    ((Finset.univ : Finset (Fin xs.length)).filter
      (fun j => z (xs.get j))).card =
    xs.countP (fun x => decide (z x)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [Finset.card_filter]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.countP_cons]
      change (if z a then (1 : ℕ) else 0) +
        (∑ j : Fin xs.length, if z (xs.get j) then 1 else 0) =
        xs.countP (fun x => decide (z x)) +
        (if decide (z a) = true then 1 else 0)
      have ht :
          (∑ j : Fin xs.length,
            if z (xs.get j) then (1 : ℕ) else 0) =
          xs.countP (fun x => decide (z x)) := by
        rw [← Finset.card_filter]
        exact ih
      rw [ht]
      by_cases hz : z a <;> simp [hz, Nat.add_comm]

/-- The cardinal of tagged concatenated OLD occurrences splits into
the literal sum of index-cardinals in every group, even with repeats. -/
theorem physical_old_index_flatMap_card
    {G U V : Type} (groups : List G) (old : G → List U)
    (tag : G → U → V) (z : V → Prop) [DecidablePred z] :
    ((Finset.univ : Finset (Fin
      (groups.flatMap (fun g => (old g).map (tag g))).length)).filter
      (fun j => z ((groups.flatMap
        (fun g => (old g).map (tag g))).get j))).card =
    (groups.map (fun g =>
      ((Finset.univ : Finset (Fin (old g).length)).filter
        (fun j => z (tag g ((old g).get j)))).card)).sum := by
  simp only [physical_old_index_card_eq_countP, List.countP_flatMap,
    List.countP_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g _
  exact (physical_old_index_card_eq_countP
    (old g) (fun x => z (tag g x))).symm

/-- Heterogeneous BIG groups: the source Fock particle type may
depend on its group. This is still an exact occurrence-index count. -/
theorem physical_old_index_sigma_flatMap_card
    {G V : Type} {U : G → Type} (groups : List G)
    (old : (g : G) → List (U g))
    (tag : (g : G) → U g → V) (z : V → Prop) [DecidablePred z] :
    ((Finset.univ : Finset (Fin
      (groups.flatMap (fun g => (old g).map (tag g))).length)).filter
      (fun j => z ((groups.flatMap
        (fun g => (old g).map (tag g))).get j))).card =
    (groups.map (fun g =>
      ((Finset.univ : Finset (Fin (old g).length)).filter
        (fun j => z (tag g ((old g).get j)))).card)).sum := by
  simp only [physical_old_index_card_eq_countP, List.countP_flatMap,
    List.countP_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g _
  exact (physical_old_index_card_eq_countP
    (old g) (fun x => z (tag g x))).symm

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostOldZeroSource -/

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

/-- Every indexed old atom reads its actual stored Fock residue.
This works at the original source row, BEFORE chronological reindexing. -/
theorem physical_actual_source_old_fock_residue_exact
    (i : ℕ) (hi : i < N) (g : BG)
    (j : Fin (Green64Fock.fockToList (((H.before i).2 g).2)).length) :
    let xs := Green64Fock.fockToList (((H.before i).2 g).2)
    (physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi).residueBefore
        (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP) =
        (xs.get j).2 := by
  dsimp only
  let xs := Green64Fock.fockToList (((H.before i).2 g).2)
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)) g
  have hn : (xs.map (fun a => a.1)).Nodup := by
    have hg := hGood.2.1
    rw [physicalProjectionPendingValues_exact] at hg
    exact Multiset.coe_nodup.mp hg
  have ha : (⟨(xs.get j).1, (xs.get j).2⟩ :
      Green64Fock.Atom (BP g) (bigMod g)) ∈
        Green64Fock.fockMultiset (((H.before i).2 g).2) := by
    have hx := List.get_mem xs j
    simpa [xs, Green64Fock.fockMultiset,
      Green64Fock.fockToList] using hx
  have hp : (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      (physicalActualLiteralSourceRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi).pendingBefore := by
    change (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP) ∈
      physicalActualLiteralPendingBefore SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i
    apply (physical_actual_literal_before_group_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i g (xs.get j).1).mpr
    exact List.mem_map.mpr ⟨xs.get j, List.get_mem xs j, rfl⟩
  exact (physical_actual_literal_row_residue_before_of_mem
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor i hi
      _ hp).trans
    (physical_literal_fock_residue_of_atom
      BP bigMod cap SP smallMod (H.before i)
      (⟨g, (xs.get j).1⟩ : PhysicalSourcePrime BP)
      hn (xs.get j).2 ha)

/-- All BIG groups of a real G row, with the original Fock OLD
index-zero subsets and no artificial numerical-prime set. -/
theorem physical_actual_source_old_zero_group_sum
    (i : ℕ) (hi : i < N) :
    (Green64Literal.oldZeroIndices
      (physicalActualLiteralSourceRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi)).card =
    ((Finset.univ.toList : List BG).map (fun g =>
      (Green64MemoryGhostOp.zeroOld
        (Green64Fock.fockToList (((H.before i).2 g).2))
        (fun a => a.2 = 0)).card)).sum := by
  let f := physicalActualLiteralSourceRow SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor i hi
  calc
    _ = ((Finset.univ.toList : List BG).map (fun g =>
        ((Finset.univ : Finset (Fin
          (Green64Fock.fockToList (((H.before i).2 g).2)).length)).filter
          (fun j => f.residueBefore
            (⟨g, ((Green64Fock.fockToList
              (((H.before i).2 g).2)).get j).1⟩ :
                PhysicalSourcePrime BP) = 0)).card)).sum := by
        exact physical_old_index_sigma_flatMap_card
          (Finset.univ.toList : List BG)
          (fun g => Green64Fock.fockToList (((H.before i).2 g).2))
          (fun g a => (⟨g, a.1⟩ : PhysicalSourcePrime BP))
          (fun p => f.residueBefore p = 0)
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro g _
      apply congrArg Finset.card
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Green64MemoryGhostOp.zeroOld]
      rw [physical_actual_source_old_fock_residue_exact
        SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
        k N H Vsmall Knu zeta theta anchor i hi g j]
      rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostTerminationSource -/

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

/-- Actual original Fock OLD occurrences have unique tagged prime
labels. The injection is derived from the physical good-orbit rule. -/
theorem physical_actual_ghost_source_old_tag_injective
    (i : ℕ) (hi : i ≤ N) (g : BG) :
    Function.Injective (fun j : Fin
      (Green64Fock.fockToList (((H.before i).2 g).2)).length =>
      (⟨g, ((Green64Fock.fockToList
        (((H.before i).2 g).2)).get j).1⟩ : PhysicalSourcePrime BP)) := by
  have hGood := (physical_finite_actual_path_good_every_visit
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi) g
  have hg := hGood.2.1
  rw [physicalProjectionPendingValues_exact] at hg
  intro a b heq
  apply (sourceFock_old_list_prime_injective (bigMod g) (cap g)
    (((H.before i).2 g).2) hg)
  exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2

/-- Every terminated OLD occurrence in the original BIG Fock
groups corresponds to one DISTINCT tagged source label. -/
theorem physical_actual_ghost_ended_values_card
    (i : ℕ) (hi : i ≤ N) :
    (physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).card =
    ∑ g : BG, ((H.ghost i g).1.1).card := by
  let t : BG → Finset (PhysicalSourcePrime BP) :=
    fun g => ((H.ghost i g).1.1).image
      (fun j => (⟨g,
        ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1⟩
         : PhysicalSourcePrime BP))
  have hpw : (↑(Finset.univ : Finset BG) : Set BG).PairwiseDisjoint t := by
    intro g _ g' _ hdiff
    apply Finset.disjoint_left.mpr
    intro p hpg hpg'
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpg
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hpg'
    have hg : g = g' :=
      congrArg Sigma.fst (hj.trans hj'.symm)
    exact hdiff hg
  change ((Finset.univ : Finset BG).biUnion t).card = _
  rw [Finset.card_biUnion hpw]
  apply Finset.sum_congr rfl
  intro g _
  exact Finset.card_image_of_injective _
    (physical_actual_ghost_source_old_tag_injective
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i hi g)

/-- The exact source literal termination Fin-indices count the
original OLD G selections across all BIG groups. -/
theorem physical_actual_source_term_indices_group_sum
    (Vsmall : SG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (i : ℕ) (hi : i < N) :
    (physicalActualLiteralTermIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).card =
    ∑ g : BG, ((H.ghost i g).1.1).card := by
  let xs := physicalActualLiteralPendingBefore SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let A := physicalActualLiteralTermIndices SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  have hn : xs.Nodup :=
    (physical_actual_literal_source_row_valid SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hprime hnum i hi).pending_nodup
  have hinj : Function.Injective xs.get :=
    List.nodup_iff_injective_get.mp hn
  have hcount : (A.image xs.get).card = A.card :=
    Finset.card_image_of_injective A hinj
  have hsource : A.image xs.get =
      physicalActualLiteralEndedValues SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i :=
    physical_actual_literal_term_index_image
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i
  rw [hsource] at hcount
  rw [← hcount]
  exact physical_actual_ghost_ended_values_card
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i (Nat.le_of_lt hi)

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostOldZeroHistory -/

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

/-- The real chronological history's G OLD-zero count equals the
source Fock-indexed count before normalization of the OLD order. -/
theorem physical_actual_literal_history_old_zero_card_source
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    (Green64Literal.oldZeroIndices
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor
        hN hprime hnum hrho hVac).rows i)).card =
    (Green64Literal.oldZeroIndices
      (physicalActualLiteralSourceRow SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor i hi)).card := by
  let B := physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  have hv : ∀ j, j < N → Green64Literal.RowValid (B j) :=
    physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor hN hprime hnum
  have hs : ∀ j, j < N →
      (B j).pendingNext.Perm (B (j+1)).pendingBefore :=
    physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor hN
  have hp : (Green64Literal.coherentPending B i).Perm (B i).pendingBefore :=
    Green64Literal.coherent_pending_perm N B hv hs i (Nat.le_of_lt hi)
  have hbase : (Green64Literal.oldZeroIndices
      (Green64Literal.pendingRebaseRow (B i) (hv i hi)
        (Green64Literal.coherentPending B i) hp)).card =
      (Green64Literal.oldZeroIndices (B i)).card :=
    Green64Literal.literal_old_zero_count_pending_rebase
      (B i) (hv i hi) _ hp
  calc
    _ = (Green64Literal.oldZeroIndices
      (Green64Literal.pendingRebaseRow (B i) (hv i hi)
        (Green64Literal.coherentPending B i) hp)).card := by
        change (Green64Literal.oldZeroIndices
          (physicalActualLiteralHistoryRows SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H
            Vsmall Knu zeta theta anchor hN hprime hnum i)).card = _
        rw [physical_actual_literal_history_rows_at
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi]
        rfl
    _ = (Green64Literal.oldZeroIndices (B i)).card := hbase
    _ = _ := by
        change (Green64Literal.oldZeroIndices (B i)).card =
          (Green64Literal.oldZeroIndices
            (physicalActualLiteralSourceRow SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig muBig k N H
              Vsmall Knu zeta theta anchor i hi)).card
        dsimp only [B, physicalActualLiteralHistoryBaseRows]
        rw [dif_pos hi]
        rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostTerminationHistory -/

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

/-- The genuine chronological OLD termination Fin indices count the
identical original witness selections after reordering. -/
theorem physical_actual_literal_history_term_card_source
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    (((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor
        hN hprime hnum hrho hVac).rows i).termIndices).card =
    (physicalActualLiteralTermIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).card := by
  let B := physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  have hv : ∀ j, j < N → Green64Literal.RowValid (B j) :=
    physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor hN hprime hnum
  have hs : ∀ j, j < N →
      (B j).pendingNext.Perm (B (j+1)).pendingBefore :=
    physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns q rho Vbig
      muBig k N H Vsmall Knu zeta theta anchor hN
  have hp : (Green64Literal.coherentPending B i).Perm (B i).pendingBefore :=
    Green64Literal.coherent_pending_perm N B hv hs i (Nat.le_of_lt hi)
  have hbase : ((Green64Literal.pendingRebaseRow (B i) (hv i hi)
      (Green64Literal.coherentPending B i) hp).termIndices).card =
      ((B i).termIndices).card :=
    Green64Literal.literal_term_count_pending_rebase
      (B i) (hv i hi) _ hp
  calc
    _ = ((Green64Literal.pendingRebaseRow (B i) (hv i hi)
      (Green64Literal.coherentPending B i) hp).termIndices).card := by
        change ((physicalActualLiteralHistoryRows SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          Vsmall Knu zeta theta anchor hN hprime hnum i).termIndices).card = _
        rw [physical_actual_literal_history_rows_at
          SP smallMod BP bigMod J ell m cap patterns
          q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum i hi]
        rfl
    _ = ((B i).termIndices).card := hbase
    _ = _ := by
        change ((B i).termIndices).card =
          (physicalActualLiteralTermIndices SP smallMod BP bigMod
            J ell m cap patterns q rho Vbig muBig k N H i).card
        dsimp only [B, physicalActualLiteralHistoryBaseRows]
        rw [dif_pos hi]
        rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostOldZeroTermCounts -/

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

/-- Correct conversion of ORIGINAL ordered group sums to
the finite BIG-group sum without changing Fock-index multiplicities. -/
theorem physical_big_group_list_sum (F : BG → ℕ) :
    ((Finset.univ.toList : List BG).map F).sum = ∑ g : BG, F g := by
  rw [← List.sum_toFinset F (Finset.nodup_toList _)]
  simp

/-- COMPLETE identification of the two OLD occurrence COUNTS:
the true indexed Fock zero-OLD and termination choices from EVERY
BIG group equal the chronological literal G-row exponents. -/
theorem physical_actual_literal_ghost_old_term_counts
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i
    (Green64Literal.oldZeroIndices f).card =
      (∑ g : BG, (Green64MemoryGhostOp.zeroOld
        (Green64Fock.fockToList (((H.before i).2 g).2))
        (fun a => a.2 = 0)).card) ∧
    f.termIndices.card = ∑ g : BG, ((H.ghost i g).1.1).card := by
  dsimp only
  constructor
  · calc
      _ = (Green64Literal.oldZeroIndices
        (physicalActualLiteralSourceRow SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H
          Vsmall Knu zeta theta anchor i hi)).card :=
        physical_actual_literal_history_old_zero_card_source
          SP smallMod BP bigMod J ell m cap patterns q rho
          Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum hrho hVac i hi
      _ = ((Finset.univ.toList : List BG).map (fun g =>
          (Green64MemoryGhostOp.zeroOld
            (Green64Fock.fockToList (((H.before i).2 g).2))
            (fun a => a.2 = 0)).card)).sum :=
        physical_actual_source_old_zero_group_sum
          SP smallMod BP bigMod J ell m cap patterns q rho Vbig
          muBig k N H Vsmall Knu zeta theta anchor i hi
      _ = _ := physical_big_group_list_sum _
  · calc
      _ = (physicalActualLiteralTermIndices SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).card :=
        physical_actual_literal_history_term_card_source
          SP smallMod BP bigMod J ell m cap patterns q rho
          Vbig muBig k N H Vsmall Knu zeta theta anchor
          hN hprime hnum hrho hVac i hi
      _ = _ := physical_actual_source_term_indices_group_sum
        SP smallMod BP bigMod J ell m cap patterns q rho
        Vbig muBig k N H Vsmall Knu zeta theta anchor
        hprime hnum i hi

end Green64FullPhysicalE

end

/-! ## PhysicalGhostOldTermCoefficient -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Aggregate the independent OLD-zero and termination powers
over ALL groups. The subtraction is legitimate because actual
selected termination indices are a subset of the zero OLD indices. -/
theorem physical_G_old_zero_term_product_algebra
    {BG : Type} [Fintype BG] (A Z : BG → ℕ)
    (hAZ : ∀ g, A g ≤ Z g) (α χ : ℂ) :
    (∏ g : BG, α ^ (A g) * χ ^ (Z g - A g)) =
    α ^ (∑ g : BG, A g) *
      χ ^ ((∑ g : BG, Z g) - (∑ g : BG, A g)) := by
  have hsum :
      (∑ g : BG, (Z g - A g)) =
      (∑ g : BG, Z g) - (∑ g : BG, A g) := by
    have hs :
        (∑ g : BG, Z g) =
        (∑ g : BG, A g) + (∑ g : BG, (Z g - A g)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      have hg := hAZ g
      omega
    omega
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [hsum]

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostOldZeroCoefficient -/

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

/-- The original source visit factor q_i, including sqrt(q) at i=0,
is exactly the q field in the fully coherent literal row. -/
theorem physical_actual_literal_ghost_row_q
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    ((physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i).q =
      sourceVisitQ q N i := by
  change (physicalActualLiteralHistoryRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum i).q = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]

/-- The FULL ORIGINAL G OLD-zero and termination coefficient.
Actual source Fock OLD positions are summed across every BIG group,
including correct subset cardinal, q_i and eta_i at visit i.
Births are handled separately, not suppressed. -/
theorem physical_actual_literal_G_old_zero_term_coeff
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i
    ((-(f.eta:ℂ) / (f.rho:ℂ)) ^ f.termIndices.card) *
      (((f.q:ℂ) / (f.rho:ℂ)^2) ^
        ((Green64Literal.oldZeroIndices f).card - f.termIndices.card)) =
    (∏ g : BG,
       ((-(sourceVisitEta q N i:ℂ) / (rho:ℂ)) ^
         ((H.ghost i g).1.1).card) *
       (((sourceVisitQ q N i:ℂ) / (rho:ℂ)^2) ^
         ((Green64MemoryGhostOp.zeroOld
           (Green64Fock.fockToList (((H.before i).2 g).2))
           (fun a => a.2 = 0)).card - ((H.ghost i g).1.1).card))) := by
  dsimp only
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  let A : BG → ℕ := fun g => ((H.ghost i g).1.1).card
  let Z : BG → ℕ := fun g => (Green64MemoryGhostOp.zeroOld
    (Green64Fock.fockToList (((H.before i).2 g).2))
    (fun a => a.2 = 0)).card
  have hAZ (g : BG) : A g ≤ Z g := by
    exact Finset.card_le_card
      (Finset.mem_powerset.mp (H.ghost i g).1.2)
  have hCounts := physical_actual_literal_ghost_old_term_counts
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig
    muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi
  dsimp only at hCounts
  obtain ⟨hOld,hTerm⟩ := hCounts
  have hFields := physical_actual_literal_ghost_row_scalar_fields
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
    k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi
  dsimp only at hFields
  obtain ⟨hEta, hRho, _⟩ := hFields
  have hQ := physical_actual_literal_ghost_row_q
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig muBig
    k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi
  have hAlg := physical_G_old_zero_term_product_algebra A Z hAZ
    (-(sourceVisitEta q N i:ℂ)/(rho:ℂ))
    ((sourceVisitQ q N i:ℂ)/(rho:ℂ)^2)
  calc
    _ = ((-(sourceVisitEta q N i:ℂ)/(rho:ℂ)) ^ (∑ g : BG, A g)) *
      (((sourceVisitQ q N i:ℂ)/(rho:ℂ)^2) ^
        ((∑ g : BG, Z g) - (∑ g : BG, A g))) := by
          rw [hEta,hRho,hQ,hTerm,hOld]
    _ = _ := hAlg.symm

end Green64FullPhysicalE

end

/-! ## PhysicalActualGhostFullRowFactor -/

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

/-- Assemble all independent groupwise scalar G factors without
discarding any BIG group or putting in extra Fock factorials. -/
theorem physical_G_four_factor_product
    (a b c d : BG → ℂ) :
    (∏ g : BG, (a g * b g)) *
      ((∏ g : BG, c g) * (∏ g : BG, d g)) =
    ∏ g : BG, a g * b g * c g * d g := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  ring

/-- The complete source literal G-row scalar is exactly the
product of all ORIGINAL Fock-indexed G-group scalars, including
OLD-zero, terminations, ghost births, factorials and genuine
muBig. This identification requires the explicit original
muBig = mu-tilde specialization. -/
theorem physical_actual_literal_full_G_row_factor
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) (hi : i < N) :
    Green64Literal.ghostWeight
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H
        Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i) =
    ∏ g : BG, physicalActualGhostFactor SP smallMod BP bigMod
      (J+ell) cap q rho N i Vbig muBig (H.before i) (H.ghost i) g := by
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  let a : BG → ℂ := fun g =>
    (-(sourceVisitEta q N i:ℂ)/(rho:ℂ)) ^
      ((H.ghost i g).1.1).card
  let b : BG → ℂ := fun g =>
    ((sourceVisitQ q N i:ℂ)/(rho:ℂ)^2) ^
      ((Green64MemoryGhostOp.zeroOld
        (Green64Fock.fockToList (((H.before i).2 g).2))
        (fun x => x.2 = 0)).card - ((H.ghost i g).1.1).card)
  let c : BG → ℂ := fun g =>
    ((1:ℂ) / (Nat.factorial ((H.ghost i g).2.1.val):ℂ)) *
      ((-(sourceVisitEta q N i:ℂ) * (Vbig g:ℂ) / (rho:ℂ)) ^
        ((H.ghost i g).2.1.val))
  let d : BG → ℂ := fun g =>
    ∏ j : Fin ((H.ghost i g).2.1.val),
      (muBig g ((H.ghost i g).2.2 j).1 : ℂ)


  have hOld := physical_actual_literal_G_old_zero_term_coeff
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig
    muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac i hi
  dsimp only at hOld
  have hBirth := physical_actual_literal_ghost_group_birth_coeff
    SP smallMod BP bigMod J ell m cap patterns q rho Vbig
    muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac hmu i hi
  dsimp only at hBirth
  calc
    Green64Literal.ghostWeight f =
      (∏ g : BG, a g * b g) *
      ((∏ g : BG, c g) * (∏ g : BG, d g)) := by
        unfold Green64Literal.ghostWeight
        rw [hOld, mul_assoc, hBirth]
    _ = (∏ g : BG, a g * b g * c g * d g) :=
      physical_G_four_factor_product a b c d
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g _
      dsimp [a,b,c,d,physicalActualGhostFactor]
      ring

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralWeightedFibre -/

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

/-- FIRST ACTUAL E weighted fibre transport: equality of the
complete original source-oriented E sums at the genuine physical
post-G state and its independently ordered before-E representative.
No artificial distinct-prime set or fixed permutation frame:
all BIG/SMALL Haar permutations, original OLD injections,
auxiliary D, Knu and Fourier phase occur in the underlying sum. -/
theorem physical_actual_E_complete_weighted_fibre_input
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (i : ℕ) (hi : i < N)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
      (H.afterG i) F =
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
      (H.beforeE i) F :=
  physical_oriented_full_E_eq_of_projected_input
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig muBig Knu
    ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
    (H.afterG i) (H.beforeE i)
    (H.E_orbit_input i hi).symm F

end Green64FullPhysicalE

end

/-! ## PhysicalActualGWeightedELiteralBridge -/

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

/-- Genuine G times FULL E weighted sum, transported to the literal
G coefficient and to the corresponding symmetric Fock E input.
Original muBig specialization remains explicit. No edgeWeight or
global memory identity is asserted by this theorem. -/
theorem physical_actual_G_times_full_E_literal_fibre
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (anchor : (g : BG) → (p : BP g) → ZMod (bigMod g p))
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) (hi : i < N)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → ℂ) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig (H.before i) (H.afterG i) (H.ghost i) *
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
      (H.afterG i) F =
    Green64Literal.ghostWeight
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H Vsmall
        Knu zeta theta anchor hN hprime hnum hrho hVac).rows i) *
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      ((i : ℝ) * zeta) theta (physicalAlternatingSign i) k
      (H.beforeE i) F := by
  rw [physical_actual_G_full_scalar_exact SP smallMod BP bigMod
    J ell cap q rho N i Vbig muBig
    (H.before i) (H.afterG i) (H.ghost i)
    (H.G_nonzero i (Nat.le_of_lt hi))]
  rw [← physical_actual_literal_full_G_row_factor
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum hrho hVac hmu i hi]
  rw [physical_actual_E_complete_weighted_fibre_input
    SP smallMod BP bigMod J ell m cap patterns q rho
    Vsmall Vbig muBig Knu zeta theta k N H i hi F]

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralSymmetryNormalization -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The literal edge BIG symmetry is EXACTLY the original
independent sigma/tau Haar pair normalization in each BIG group.
The independent SMALL Haar pair mass remains a separate factor. -/
theorem physical_literal_edge_big_pair_mass
    {P BG : Type} [DecidableEq P] [Fintype BG]
    (M : ℕ)
    (f : Green64Literal.SourceRow (P := P) BG (fun _ => M)) :
    Green64Literal.edgeSymmetryWeight f =
      (bigEndpointPairMass (BG := BG) M : ℂ) := by
  unfold Green64Literal.edgeSymmetryWeight bigEndpointPairMass
  push_cast
  apply Finset.prod_congr rfl
  intro g _
  simp only [Green64SmallHaar.permutationPairMass]
  push_cast
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralFreshMass -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Product under literal list flatMap, preserving every source
occurrence without converting to a set of (possibly repeated) primes. -/
theorem physical_list_prod_flatMap {G : Type}
    (xs : List G) (f : G → List ℂ) :
    (xs.flatMap f).prod = (xs.map (fun g => (f g).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.flatMap_cons, List.prod_append,
        List.map_cons, List.prod_cons, ih]

/-- The exact source BIG-group/Finset-slot product for arbitrary
indexed fresh draws (including prime labels repeated in distinct
draws). No deduplication is ever performed. -/
theorem physical_group_slot_prod
    {BG S : Type} [Fintype BG] [DecidableEq BG]
    [DecidableEq S] (fresh : BG → Finset S)
    (w : BG → S → ℂ) :
    ((Finset.univ.toList : List BG).flatMap (fun g =>
      (fresh g).toList.map (w g))).prod =
    ∏ g : BG, ∏ j ∈ fresh g, w g j := by
  rw [physical_list_prod_flatMap]
  rw [← List.prod_toFinset
    (fun g => ((fresh g).toList.map (w g)).prod)
    (Finset.nodup_toList (Finset.univ : Finset BG))]
  simp only [Finset.toList_toFinset]
  apply Finset.prod_congr rfl
  intro g _
  simpa only [Finset.toList_toFinset] using
    (List.prod_toFinset (w g)
      (Finset.nodup_toList (fresh g))).symm

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralFreshMassActual -/

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

/-- Real literal E fresh TARGET slots, with the independent target
permutation tau, survive both chronological rebasings unchanged. -/
theorem physical_actual_literal_history_fresh_target
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    ((physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
      zeta theta anchor hN hprime hnum hrho hVac).rows i).freshTarget =
    physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i := by
  change (physicalActualLiteralHistoryRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
    zeta theta anchor hN hprime hnum i).freshTarget = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralFreshCoefficient -/

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
/-- Each original source target tau slot contributes one muBig factor.
The real pattern-unshared/promote complement is retained as an indexed
Finset for each BIG group, even when values repeat between slots. -/
theorem physical_actual_E_fresh_indexed_mu (i : ℕ) :
    ((physicalActualLiteralFreshTarget SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).map
      (fun p => (muBig p.1 p.2 : ℂ))).prod =
    ∏ g : BG, ∏ j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      (((H.edge i).2.2.1.bigChoice g).2.2.1),
      (muBig g (((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j)) : ℂ) := by
  unfold physicalActualLiteralFreshTarget
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  exact physical_group_slot_prod
    (fun g => orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      (((H.edge i).2.2.1.bigChoice g).2.2.1))
    (fun g j => (muBig g
      (((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j)) : ℂ))

/-- Actual E fresh-target literal mu mass equals the COMPLETE
source-oriented fresh integration weight. Source muBig specialization
is explicit; no deduplication of different target occurrence indices. -/
theorem physical_actual_literal_E_fresh_coefficient
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    (f.freshTarget.map (Green64Literal.sourceMu f)).prod =
    ∏ g : BG, ∏ j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      (((H.edge i).2.2.1.bigChoice g).2.2.1),
      (muBig g (((H.edge i).2.2.1.bigChoice g).1
        (((H.edge i).2.2.1.tauBig g) j)) : ℂ) := by
  dsimp only
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  have hFresh : f.freshTarget =
      physicalActualLiteralFreshTarget SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i :=
    physical_actual_literal_history_fresh_target
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum hrho hVac i hi
  calc
    (f.freshTarget.map (Green64Literal.sourceMu f)).prod =
      (f.freshTarget.map (fun p : PhysicalSourcePrime BP =>
        (muBig p.1 p.2 : ℂ))).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro p hp
          exact (physical_actual_literal_row_birth_mu
            SP smallMod BP bigMod J ell m cap patterns
            q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
            hN hprime hnum hrho hVac i hi p).trans (hmu p.1 p.2).symm
    _ = _ := by
      rw [hFresh]
      exact physical_actual_E_fresh_indexed_mu
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H i

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralAuxiliaryMass -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Dependent original slot products retain every slot, including
distinct independent auxiliary draws with equal prime values. -/
theorem physical_dependent_indexed_list_prod
    {G : Type} [Fintype G] [DecidableEq G]
    {S : G → Type} [∀ g, Fintype (S g)]
    [∀ g, DecidableEq (S g)]
    (w : (g : G) → S g → ℂ) :
    ((Finset.univ.toList : List G).flatMap (fun g =>
      (Finset.univ.toList : List (S g)).map (w g))).prod =
    ∏ g : G, ∏ j : S g, w g j := by
  rw [physical_list_prod_flatMap]
  rw [← List.prod_toFinset
    (fun g => ((Finset.univ.toList : List (S g)).map (w g)).prod)
    (Finset.nodup_toList (Finset.univ : Finset G))]
  simp only [Finset.toList_toFinset]
  apply Finset.prod_congr rfl
  intro g hg
  simpa only [Finset.toList_toFinset] using
    (List.prod_toFinset (w g)
      (Finset.nodup_toList (Finset.univ : Finset (S g)))).symm
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
/-- Exact original D auxiliary measure: each C_g slot is drawn
with 1/(V_g p), not the baseline-tilted sourceMu for active births.
No condition that auxiliary draws are distinct is introduced. -/
theorem physical_actual_E_auxiliary_source_mass (i : ℕ) :
    ((physicalActualLiteralAuxiliaryPrimes SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i).map
      (fun p => (((1:ℝ) /
        (Vbig p.1 * (bigMod p.1 p.2 : ℝ))) : ℂ))).prod =
    (sourceAuxMass BP bigMod J m Vbig
      (patterns (H.edge i).1) (H.edge i).2.1 : ℂ) := by
  unfold physicalActualLiteralAuxiliaryPrimes
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  rw [physical_dependent_indexed_list_prod
    (w := fun g (j : ↥((patterns (H.edge i).1).free g)) =>
      (((1:ℝ) / (Vbig g *
        (bigMod g ((H.edge i).2.1 g j) : ℝ))) : ℂ))]
  simp only [sourceAuxMass, Complex.ofReal_prod,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one]

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralAuxiliaryCoefficient -/

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
/-- Independent auxiliary sampling survives chronological, endpoint
and first-birth rebasings. The measure is ordinary, not tilted. -/
theorem physical_actual_literal_history_auxiliary_fields
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    f.auxiliaryPrimes = physicalActualLiteralAuxiliaryPrimes
      SP smallMod BP bigMod J ell m cap patterns q rho
      Vbig muBig k N H i ∧
    f.auxiliaryMeasure = (fun p : PhysicalSourcePrime BP =>
      1 / (Vbig p.1 * (bigMod p.1 p.2 : ℝ))) := by
  dsimp only
  change
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).auxiliaryPrimes = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).auxiliaryMeasure = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  exact ⟨rfl, rfl⟩

/-- Full literal auxiliary C_g mass matches the source
independent D-draw coefficient, slot by slot, with multiplicities. -/
theorem physical_actual_literal_E_auxiliary_coefficient
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    (f.auxiliaryPrimes.map (fun p => (f.auxiliaryMeasure p : ℂ))).prod =
    (sourceAuxMass BP bigMod J m Vbig
      (patterns (H.edge i).1) (H.edge i).2.1 : ℂ) := by
  dsimp only
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  obtain ⟨hAux,hMeasure⟩ :=
    physical_actual_literal_history_auxiliary_fields
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum hrho hVac i hi
  rw [hAux, hMeasure]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one] using
    (physical_actual_E_auxiliary_source_mass
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H i)

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralPhaseCoefficient -/

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
/-- Exact source Fourier data in the fully normalized literal row.
Both BIG sigma/tau families, the independently permuted SMALL sigma
inside D, original auxiliary draws, orientation and time exponent
remain intact; the kernel K occurs exactly once. -/
theorem physical_actual_literal_E_phase_fields
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    f.kernelK = Knu (H.edge i).1 (H.edge i).2.1
      (fun g j => ((H.beforeE i).2 g).1
        ((H.edge i).2.2.1.sigmaBig g j))
      (fun g j => ((H.edge i).2.2.1.bigChoice g).1
        ((H.edge i).2.2.1.tauBig g j)) ∧
    f.divisorD = sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
      (H.beforeE i) (H.edge i).2.2.1.sigmaBig
      (H.edge i).2.2.2.1 ∧
    f.zeta = (i : ℝ) * zeta ∧ f.theta = theta ∧
    f.orientation = physicalAlternatingSign i ∧ f.k = k := by
  dsimp only
  change
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).kernelK = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).divisorD = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).zeta = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).theta = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).orientation = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).k = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The literal Fourier part at a TRUE source physical witness is
precisely the original signed K_nu D^(i zeta) additive phase.
No fixed-D surrogate and no second K_nu multiplier. -/
theorem physical_actual_literal_E_source_phase_once
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    Green64Literal.orientedKernel f *
      Green64Literal.additivePhase f =
    originalEdgeScalar
      (Knu (H.edge i).1 (H.edge i).2.1
        (fun g j => ((H.beforeE i).2 g).1
          ((H.edge i).2.2.1.sigmaBig g j))
        (fun g j => ((H.edge i).2.2.1.bigChoice g).1
          ((H.edge i).2.2.1.tauBig g j)))
      ((i : ℝ) * zeta) theta
      (sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap (patterns (H.edge i).1) (H.edge i).2.1
        (H.beforeE i) (H.edge i).2.2.1.sigmaBig
        (H.edge i).2.2.2.1)
      (physicalAlternatingSign i) k := by
  dsimp only
  let f := (physicalActualLiteralHistory SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
  obtain ⟨hK,hD,hZ,hT,hOrient,hk⟩ :=
    physical_actual_literal_E_phase_fields SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum
      hrho hVac i hi
  change Green64Literal.orientedKernel f *
    Green64Literal.additivePhase f = _
  rw [source_original_scalar_is_literal_phase f]
  rw [hK,hD,hZ,hT,hOrient,hk]

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralSmallHaarFactor -/

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
/-- The fully coherent literal smallFactor is the actual
independent SMALL sigma/tau physical congruence-and-q kernel.
The SMALL pair Haar mass is deliberately NOT inserted by this
identity; in the original physical source it is external. -/
theorem physical_actual_literal_E_small_factor
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    f.smallFactor =
    Green64SmallHaar.groupPermutedKernel
      SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell)
      (sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns (H.edge i).1) (H.edge i).2.1 (H.beforeE i)
        (H.edge i).2.2.1.sigmaBig (H.edge i).2.2.2.1
        (physicalAlternatingSign i) k)
      (fun _ _ => (1:ℂ)) (H.edge i).2.2.2.1
      (H.edge i).2.2.2.2 (H.beforeE i).1
      ((H.edge i).2.2.1.smallTarget) := by
  dsimp only
  change
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).smallFactor = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]

  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  rfl

/-- BIG sigma/tau orbit mass, kept separate from SMALL Haar. -/
theorem physical_actual_literal_E_big_symmetry
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) :
    Green64Literal.edgeSymmetryWeight
      ((physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i) =
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) := by
  exact physical_literal_edge_big_pair_mass (J+ell) _

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralPromotionCoefficient -/

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
/-- Original target tau promotions are indexed, and their
V_g^{-1} weight equals the groupwise count of selected OLD
target slots; no fresh, shared or auxiliary draws are counted. -/
theorem physical_actual_E_promotion_weight_indexed
    (i : ℕ) (hi : i < N) :
    (∏ j ∈ physicalActualLiteralPromotionIndices SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig
        muBig k N H i,
      ((1:ℂ) / (Vbig
        ((physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get j).1:ℂ))) =
    ∏ g : BG, ((1:ℂ) / (Vbig g:ℂ)) ^
      (((H.edge i).2.2.1.bigChoice g).2.2.1.card) := by
  let xs := physicalActualLiteralRawTargetList SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H i
  let S := physicalActualLiteralPromotionIndices SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig muBig k N H i
  let ptn : BG → Finset (Fin (J+ell)) := fun g =>
    (((H.edge i).2.2.1.bigChoice g).2).2.1
  let slots : Finset (Σ _ : BG, Fin (J+ell)) :=
    (Finset.univ).filter (fun a => a.2 ∈ ptn a.1)
  let tgt : (Σ _ : BG, Fin (J+ell)) → PhysicalSourcePrime BP :=
    fun a => actualLiteralCanonicalTargetSlot SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i a.1 a.2
  let w : PhysicalSourcePrime BP → ℂ :=
    fun p => (1:ℂ) / (Vbig p.1:ℂ)
  have hinj : Function.Injective xs.get :=
    List.nodup_iff_injective_get.mp
      (physical_actual_literal_raw_target_nodup SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i hi)
  have htgt : Function.Injective tgt :=
    physical_actual_literal_target_slot_injective SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i hi
  have hslots : slots = (Finset.univ : Finset BG).sigma ptn := by
    ext ⟨g,j⟩
    simp [slots, ptn]
  change (∏ j ∈ S, w (xs.get j)) = _
  calc
    (∏ j ∈ S, w (xs.get j)) =
      ∏ p ∈ physicalActualLiteralPromotionValues SP smallMod
        BP bigMod J ell m cap patterns q rho Vbig muBig k N H i,
        w p := by
          rw [← physical_actual_literal_promotion_index_image]
          exact (Finset.prod_image (s := S) (g := xs.get)
            (f := w) (fun a ha b hb heq => hinj heq)).symm
    _ = ∏ a ∈ slots, w (tgt a) := by
      change (∏ p ∈ slots.image tgt, w p) = _
      exact Finset.prod_image (s := slots) (g := tgt)
        (f := w) (fun a ha b hb heq => htgt heq)
    _ = ∏ g : BG, ∏ j ∈ ptn g, ((1:ℂ)/(Vbig g:ℂ)) := by
      rw [hslots, Finset.prod_sigma]
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro g hg
      simp only [Finset.prod_const]
      rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralPromotionFields -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 1600000

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
/-- Reordered literal history retains precisely the original
promotion index subset and unpermuted RAW target slot-index list. -/
theorem physical_actual_literal_E_promotion_fields
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let f := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    f.targetEndpoint = physicalActualLiteralRawTargetList SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i ∧
    f.labelGroup = physicalSourcePrimeGroup BP ∧ f.groupV = Vbig := by
  dsimp only
  change
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).targetEndpoint = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).labelGroup = _ ∧
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i).groupV = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  simp only [physicalActualLiteralHistoryRow,
    Green64Literal.freshBeforeRebase,
    physicalActualLiteralHistoryCoherentRow,
    Green64Literal.coherentPendingRow,
    Green64Literal.pendingRebaseRow,
    physicalActualLiteralHistoryBaseRows, dif_pos hi,
    physicalActualLiteralHistoryEndpointRow,
    Green64Literal.endpointActiveRow,
    physicalActualLiteralHistoryScalarRow]
  exact ⟨rfl, rfl, rfl⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralPromotionRebase -/

section

open Classical
open scoped BigOperators

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G]
variable {slots : G → ℕ}

noncomputable def originalPromotionFactor
    (f : SourceRow (P := P) G slots) : ℂ :=
  ∏ j : f.promotionSlots,
    ((1:ℂ) /
      (f.groupV (f.labelGroup (f.targetEndpoint.get j.val)) : ℂ))

theorem original_promotion_factor_endpoint_active
    (f : SourceRow (P := P) G slots) :
    originalPromotionFactor (endpointActiveRow f) =
      originalPromotionFactor f := rfl

theorem original_promotion_factor_fresh_rebase
    (f : SourceRow (P := P) G slots) (xs : List P) :
    originalPromotionFactor (freshBeforeRebase f xs) =
      originalPromotionFactor f := rfl
theorem original_promotion_factor_pending_rebase
    (f : SourceRow (P := P) G slots)
    (h : RowValid f) (xs : List P)
    (hp : xs.Perm f.pendingBefore) :
    originalPromotionFactor (pendingRebaseRow f h xs hp) =
      originalPromotionFactor f := rfl

theorem original_promotion_factor_update_q
    (f : SourceRow (P := P) G slots) (q' : ℝ) :
    originalPromotionFactor {f with q := q'} =
      originalPromotionFactor f := rfl

end Green64Literal

end

/-! ## PhysicalActualELiteralPromotionHistoryFixed -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 600000

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
/-- Actual indexed OLD promotion scalar in the FULL chronological
original history; invariant under genuine OLD occurrence reindexing.
Never replace the OLD injection by a set of numerical primes. -/
theorem physical_actual_literal_E_promotion_coefficient
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    Green64Literal.originalPromotionFactor
      ((physicalActualLiteralHistory SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H Vsmall Knu
        zeta theta anchor hN hprime hnum hrho hVac).rows i) =
    ∏ g : BG, ((1:ℂ)/(Vbig g:ℂ)) ^
      (((H.edge i).2.2.1.bigChoice g).2.2.1.card) := by
  change Green64Literal.originalPromotionFactor
    (physicalActualLiteralHistoryRows SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum i) = _
  rw [physical_actual_literal_history_rows_at
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
    hN hprime hnum i hi]
  unfold physicalActualLiteralHistoryRow
  rw [Green64Literal.original_promotion_factor_fresh_rebase]
  unfold physicalActualLiteralHistoryCoherentRow
  unfold Green64Literal.coherentPendingRow
  rw [Green64Literal.original_promotion_factor_pending_rebase]
  unfold physicalActualLiteralHistoryBaseRows
  rw [dif_pos hi]
  unfold physicalActualLiteralHistoryEndpointRow
  rw [Green64Literal.original_promotion_factor_endpoint_active]
  unfold physicalActualLiteralHistoryScalarRow
  rw [Green64Literal.original_promotion_factor_update_q]
  unfold Green64Literal.originalPromotionFactor
  change
    (∏ j : (physicalActualLiteralPromotionIndices SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig muBig k N H i),
      ((1:ℂ)/(Vbig
        ((physicalActualLiteralRawTargetList SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H i).get j.val).1:ℂ))) = _
  have h := physical_actual_E_promotion_weight_indexed
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H i hi
  exact (Finset.prod_coe_sort
    (physicalActualLiteralPromotionIndices SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H i)
    (fun j => ((1:ℂ) /
      (Vbig ((physicalActualLiteralRawTargetList SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).get j).1:ℂ)))).trans h

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralRhoRebase -/

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
/-- Both original E rho exponents keep their EXACT zero-index
multiplicities under chronological OLD Fock reindexing.
These are not cardinalities of unlabelled numerical prime sets. -/
theorem physical_actual_literal_E_rho_count_rebase
    (hN : 0 < N)
    (hprime : ∀ g : BG, ∀ p : BP g, Nat.Prime (bigMod g p))
    (hnum : Function.Injective (physicalSourcePrimeValue BP bigMod))
    (hrho : 0 < rho)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (i : ℕ) (hi : i < N) :
    let lit := (physicalActualLiteralHistory SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor hN hprime hnum hrho hVac).rows i
    let raw := physicalActualLiteralSourceRow SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H
      Vsmall Knu zeta theta anchor i hi
    (Green64Literal.visitZeroIndices lit).card =
      (Green64Literal.visitZeroIndices raw).card ∧
    (Green64Literal.targetZeroIndices lit).card =
      (Green64Literal.targetZeroIndices raw).card := by
  dsimp only
  let B := physicalActualLiteralHistoryBaseRows SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H
    Vsmall Knu zeta theta anchor hN
  have hv : ∀ j, j < N → Green64Literal.RowValid (B j) :=
    physical_actual_literal_history_base_row_valid
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor
      hN hprime hnum
  have hs : ∀ j, j < N →
      (B j).pendingNext.Perm (B (j+1)).pendingBefore :=
    physical_actual_literal_history_base_pending_step
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N H Vsmall Knu zeta theta anchor hN
  have hp : (Green64Literal.coherentPending B i).Perm
      (B i).pendingBefore :=
    Green64Literal.coherent_pending_perm N B hv hs
      i (Nat.le_of_lt hi)
  have hVisit := Green64Literal.literal_visit_zero_count_pending_rebase
    (B i) (hv i hi) _ hp
  have hTarget := Green64Literal.literal_target_zero_count_pending_rebase
    (B i) (hv i hi) _ hp
  constructor
  · calc
      (Green64Literal.visitZeroIndices
        ((physicalActualLiteralHistory SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H Vsmall
          Knu zeta theta anchor hN hprime hnum hrho hVac).rows i)).card =
        (Green64Literal.visitZeroIndices
          (Green64Literal.pendingRebaseRow (B i) (hv i hi)
            (Green64Literal.coherentPending B i) hp)).card := by
            change (Green64Literal.visitZeroIndices
              (physicalActualLiteralHistoryRows SP smallMod BP bigMod
                J ell m cap patterns q rho Vbig muBig k N H
                Vsmall Knu zeta theta anchor hN hprime hnum i)).card = _
            rw [physical_actual_literal_history_rows_at
              SP smallMod BP bigMod J ell m cap patterns q rho
              Vbig muBig k N H Vsmall Knu zeta theta anchor
              hN hprime hnum i hi]
            rfl
      _ = (Green64Literal.visitZeroIndices (B i)).card := hVisit
      _ = _ := by
        change (Green64Literal.visitZeroIndices (B i)).card =
          (Green64Literal.visitZeroIndices
            (physicalActualLiteralSourceRow SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig muBig k N H
              Vsmall Knu zeta theta anchor i hi)).card
        dsimp only [B, physicalActualLiteralHistoryBaseRows]
        rw [dif_pos hi]
        rfl
  · calc
      (Green64Literal.targetZeroIndices
        ((physicalActualLiteralHistory SP smallMod BP bigMod
          J ell m cap patterns q rho Vbig muBig k N H Vsmall
          Knu zeta theta anchor hN hprime hnum hrho hVac).rows i)).card =
        (Green64Literal.targetZeroIndices
          (Green64Literal.pendingRebaseRow (B i) (hv i hi)
            (Green64Literal.coherentPending B i) hp)).card := by
            change (Green64Literal.targetZeroIndices
              (physicalActualLiteralHistoryRows SP smallMod BP bigMod
                J ell m cap patterns q rho Vbig muBig k N H
                Vsmall Knu zeta theta anchor hN hprime hnum i)).card = _
            rw [physical_actual_literal_history_rows_at
              SP smallMod BP bigMod J ell m cap patterns q rho
              Vbig muBig k N H Vsmall Knu zeta theta anchor
              hN hprime hnum i hi]
            rfl
      _ = (Green64Literal.targetZeroIndices (B i)).card := hTarget
      _ = _ := by
        change (Green64Literal.targetZeroIndices (B i)).card =
          (Green64Literal.targetZeroIndices
            (physicalActualLiteralSourceRow SP smallMod BP bigMod
              J ell m cap patterns q rho Vbig muBig k N H
              Vsmall Knu zeta theta anchor i hi)).card
        dsimp only [B, physicalActualLiteralHistoryBaseRows]
        rw [dif_pos hi]
        rfl

end Green64FullPhysicalE

end

/-! ## PhysicalActualELiteralFockZeroIndices -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Source Fock old-zero cardinal is exactly the index-filter count
on its genuine ordered Fock list; no quotient by prime values. -/
theorem physical_E_fock_list_zero_indices
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    {B : ℕ} (s : Green64Fock.FockState
      (Green64Fock.Atom P modulus) B) :
    ((Finset.univ : Finset (Fin (Green64Fock.fockToList s).length)).filter
      (fun j => ((Green64Fock.fockToList s).get j).2 = 0)).card =
    Green64PhysicalEdge.oldZeroCount s := by
  let e : Fin (Green64Fock.fockToList s).length ≃
      Fin s.1.val := finCongr (Green64Fock.fockToList_length s)
  have hget (j : Fin (Green64Fock.fockToList s).length) :
      (Green64Fock.fockToList s).get j = s.2 (e j) := by
    have hcast : Fin.cast (Green64Fock.fockToList_length s) j = e j :=
      Fin.ext rfl
    calc
      _ = s.2 (Fin.cast (Green64Fock.fockToList_length s) j) :=
        List.get_ofFn s.2 j
      _ = s.2 (e j) := congrArg s.2 hcast
  let A : Finset (Fin (Green64Fock.fockToList s).length) :=
    Finset.univ.filter (fun j => ((Green64Fock.fockToList s).get j).2 = 0)
  let B0 : Finset (Fin s.1.val) :=
    Finset.univ.filter (fun j => (s.2 j).2 = 0)
  have he : A.image e = B0 := by
    ext j
    simp only [A, B0, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rwa [hget] at ha
    · intro hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      rw [hget, e.apply_symm_apply]
      exact hj
  change A.card = B0.card
  calc
    A.card = (A.image e).card :=
      (Finset.card_image_of_injective A e.injective).symm
    _ = B0.card := by rw [he]

end Green64FullPhysicalE

end

