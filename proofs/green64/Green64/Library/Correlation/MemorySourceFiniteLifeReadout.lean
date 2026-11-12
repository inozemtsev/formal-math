module

public import Green64.Library.Correlation.MemorySourceRootLifespanReadout
public import Green64.Library.Correlation.Part018

@[expose] public section

/-!
# Correlation / MemorySourceFiniteLifeReadout

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemorySourceFiniteLifeReadout -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Erase only the proved finite endpoint bounds. -/
def memoryFiniteLifeErase {n : ℕ} (l : MemoryLifespanChoice n) : Option (ℕ × ℕ) :=
  l.map (fun az => (az.1.val, az.2.val))

theorem memory_life_fits_bounded {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (n : ℕ)
    (life : P → Option (ℕ × ℕ)) (hf : PhysicalLifeFits c n life)
    (p : P) (az : ℕ × ℕ) (he : life p = some az) :
    az.1 < n ∧ az.2 < n := by
  have h := hf p
  simp only [he] at h
  exact ⟨lt_of_le_of_lt h.1 h.2.1, h.2.1⟩

/-- Derived finite carrier, not an arbitrary bound on a source path. -/
def memoryLifeFitsToFinite {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (n : ℕ)
    (life : P → Option (ℕ × ℕ)) (hf : PhysicalLifeFits c n life)
    (p : P) : MemoryLifespanChoice n :=
  match he : life p with
  | none => none
  | some az => some (⟨az.1, (memory_life_fits_bounded c n life hf p az he).1⟩,
                    ⟨az.2, (memory_life_fits_bounded c n life hf p az he).2⟩)

theorem memory_life_fits_finite_erase {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (n : ℕ)
    (life : P → Option (ℕ × ℕ)) (hf : PhysicalLifeFits c n life) (p : P) :
    memoryFiniteLifeErase (memoryLifeFitsToFinite c n life hf p) = life p := by
  unfold memoryLifeFitsToFinite
  split <;> simp_all [memoryFiniteLifeErase]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Every actual nonzero source root has a profile IN THE EXACT finite
lifespan carrier of the pinned global sum, preserving all five physical
clock equivalences. No independent-residue or reverse-fibre assumption. -/
theorem memory_source_root_finite_life_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hR : 0 < R)
    (hnum : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hR w
    ∃ life : (g : BG) → BP g → MemoryLifespanChoice (2*R+1),
      ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        k (2*R) H g) (2*R+1) (fun p => memoryFiniteLifeErase (life g p)) := by
  dsimp only
  obtain ⟨life, hf, _⟩ := memory_source_root_unique_lifespan_readout
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
    zeta theta k R hR hnum w
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hR w
  let c := fun g => physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    k (2*R) H g
  refine ⟨fun g => memoryLifeFitsToFinite (c g) (2*R+1) (life g) (hf g), ?_⟩
  intro g
  have he : (fun p => memoryFiniteLifeErase
      (memoryLifeFitsToFinite (c g) (2*R+1) (life g) (hf g) p)) = life g := by
    funext p
    exact memory_life_fits_finite_erase _ _ _ _ p
  rw [he]
  exact hf g
end Green64FullPhysicalE

end

end

