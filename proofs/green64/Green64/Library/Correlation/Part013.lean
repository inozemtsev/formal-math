module

public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part012

@[expose] public section

/-!
# Correlation / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemorySourceTraceTerminalVacuum -/

section

open Classical
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

/-- A nonzero actual trace has the original terminal G output
vacuum; no boundary normalization is assumed. -/
theorem memory_source_trace_terminal_vacuum
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hw : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t ≠ 0) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k remaining start y seen t
          (Fin.last remaining)).2.1) = 1 := by
  induction remaining generalizing start y seen with
  | zero =>
    change physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        t.val.2.1) = 1
    by_cases hv : ∀ g : BG,
        ((physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap t.val.2.1).2 g).2 = 0
    · simp [physicalVacuum, hv]
    · have hz : physicalOrientedIndexedTerminalWeight
        SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig muBig N start y t.val = 0 := by
        simp [physicalOrientedIndexedTerminalWeight, physicalVacuum, hv]
      exact False.elim (hw hz)
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    have htail : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N n (start+1) yNext seenNext tail ≠ 0 := by
      intro hz
      apply hw
      change (physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta (physicalAlternatingSign start)
        k y ab.val) *
        (memorySourceIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N n (start+1) yNext seenNext tail) = 0
      rw [hz, mul_zero]
    change physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1) yNext seenNext tail
          (Fin.last n)).2.1) = 1
    exact ih (start+1) yNext seenNext tail htail
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootTerminalVacuum -/

section

open Classical
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

/-- A nonzero actual trace has the original terminal G output
vacuum; no boundary normalization is assumed. -/
theorem physical_oriented_trace_terminal_vacuum
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hw : physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining start y seen t ≠ 0) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k remaining start y seen t
          (Fin.last remaining)).2.1) = 1 := by
  induction remaining generalizing start y seen with
  | zero =>
    change physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        t.val.2.1) = 1
    by_cases hv : ∀ g : BG,
        ((physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap t.val.2.1).2 g).2 = 0
    · simp [physicalVacuum, hv]
    · have hz : physicalOrientedIndexedTerminalWeight
        SP smallMod BP bigMod J ell cap
        q rho Vsmall Vbig muBig N start y t.val = 0 := by
        simp [physicalOrientedIndexedTerminalWeight, physicalVacuum, hv]
      exact False.elim (hw hz)
  | succ n ih =>
    rcases t with ⟨ab, tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    have htail : physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N n (start+1) yNext seenNext tail ≠ 0 := by
      intro hz
      apply hw
      change (physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        Knu ((start : ℝ)*zeta) theta (physicalAlternatingSign start)
        k y ab.val) *
        (physicalOrientedIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N n (start+1) yNext seenNext tail) = 0
      rw [hz, mul_zero]
    change physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1) yNext seenNext tail
          (Fin.last n)).2.1) = 1
    exact ih (start+1) yNext seenNext tail htail
end Green64FullPhysicalE

end

/-! ## MemorySourceRootTerminalVacuum -/

section

open Classical
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

/-- True terminal vacuum of each contributing original root trace. -/
theorem memory_source_root_terminal_vacuum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k (2*R) 0
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
          (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
          w.val.2 (Fin.last (2*R))).2.1) = 1 := by
  have hw : memorySourceRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    w.property
  have htrace : memorySourceIndexedTraceWeight
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k (2*R) (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 ≠ 0 := by
    intro hz
    apply hw
    simp [memorySourceRootIndexedWeight, hz]
  exact memory_source_trace_terminal_vacuum
    SP smallMod BP bigMod J ell m cap patterns
    q rho (2*R) Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k (2*R) 0
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      w.val.1).toFinset w.val.2 htrace
end Green64FullPhysicalE

end

/-! ## PhysicalOrientedContributingTerminalVacuum -/

section

open Classical
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

/-- True terminal vacuum of each contributing original root trace. -/
theorem physical_oriented_contributing_terminal_vacuum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : PhysicalOrientedContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (physicalOrientedTraceGWitness SP smallMod BP bigMod
          J ell m cap patterns k (2*R) 0
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
          (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
          w.val.2 (Fin.last (2*R))).2.1) = 1 := by
  have hw : physicalOrientedRootIndexedWeight SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R w.val ≠ 0 :=
    (Finset.mem_filter.mp w.property).2
  have htrace : physicalOrientedIndexedTraceWeight
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k (2*R) (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap
        w.val.1).toFinset w.val.2 ≠ 0 := by
    intro hz
    apply hw
    simp [physicalOrientedRootIndexedWeight, hz]
  exact physical_oriented_trace_terminal_vacuum
    SP smallMod BP bigMod J ell m cap patterns
    q rho (2*R) Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k (2*R) 0
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
    (physicalInitialBirths SP smallMod BP bigMod J ell cap
      w.val.1).toFinset w.val.2 htrace
end Green64FullPhysicalE

end

/-! ## MemorySourceRootPathTerminalVacuum -/

section

open Classical
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

/-- Terminal vacuum required by the true weighted literal-fibre theorem. -/
theorem memory_source_root_to_path_terminal_vacuum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R)
    (w : MemorySourceContributingRootTrace SP smallMod BP
      bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R) :
    physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        ((memory_source_root_to_actual_witness_path SP smallMod
          BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
          zeta theta k R hR w).afterG (2*R))) = 1 := by
  have hh := memory_source_root_terminal_vacuum
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vsmall Vbig Knu zeta theta k R w
  have hidx :
      (⟨(2*R) % (2*R+1),
        Nat.mod_lt (2*R) (Nat.succ_pos (2*R))⟩ : Fin (2*R+1)) =
      Fin.last (2*R) := by
    apply Fin.ext
    change (2*R) % (2*R+1) = 2*R
    exact Nat.mod_eq_of_lt (Nat.lt_succ_self (2*R))
  change physicalVacuum SP smallMod BP bigMod J ell
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap
      (physicalOrientedTraceGWitness SP smallMod BP bigMod
        J ell m cap patterns k (2*R) 0
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
        (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
        w.val.2
        (⟨(2*R) % (2*R+1), Nat.mod_lt (2*R) (Nat.succ_pos (2*R))⟩ : Fin (2*R+1))).2.1) = 1
  rw [hidx]
  exact hh
end Green64FullPhysicalE

end

