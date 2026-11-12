module

public import Green64.Library.Correlation.Part013
public import Green64.Library.Correlation.Part008

@[expose] public section

/-!
# Correlation / MemorySourceRootLifespanReadout

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemorySourceRootLifespanReadout -/

section

open Classical
noncomputable section
namespace Green64FullPhysicalE

/-- Endpoint uniqueness for the exact physical readout, used immediately below.
It does not assert an augmented-history bijection or a weighted inverse. -/
private theorem memory_physical_life_fits_unique
    {P : Type} [DecidableEq P] (c : ActualSourceSetClock P) (T : ℕ)
    (l m : P → Option (ℕ × ℕ)) (hl : PhysicalLifeFits c T l)
    (hm : PhysicalLifeFits c T m) : l = m := by
  funext p
  have hlnone_some (hn : ∀ i, p ∉ c.active i ∧ p ∉ c.pending i ∧ p ∉ c.ghost i)
      (a z : ℕ)
      (hs : a ≤ z ∧ z < T ∧ (a = z → p ∈ c.active a) ∧
        ∀ i, (p ∈ c.active i → a ≤ i ∧ i ≤ z) ∧
          (p ∈ c.pending i ↔ a < i ∧ i ≤ z ∧ p ∉ c.active i) ∧
          (p ∈ (c.pending i \ c.ended i) ∪ c.ghost i ↔ a ≤ i ∧ i < z ∧ p ∉ c.active i) ∧
          (p ∈ c.fresh i ∪ c.ghost i ↔ a = i) ∧
          (p ∈ c.ended i ∪ (c.active i \ (c.shared i ∪ c.stored i)) ↔ z = i)) : False := by
    have hna := (hn a).1
    have haz : a < z := lt_of_le_of_ne hs.1 (fun he => hna (hs.2.2.1 he))
    have hafter := (hs.2.2.2 a).2.2.1.mpr ⟨le_rfl, haz, hna⟩
    rcases Finset.mem_union.mp hafter with hp | hp
    · exact (hn a).2.1 (Finset.mem_sdiff.mp hp).1
    · exact (hn a).2.2 hp
  have h1 := hl p
  have h2 := hm p
  cases hL : l p with
  | none =>
    cases hM : m p with
    | none => rfl
    | some az =>
      exact False.elim (hlnone_some (by simpa [hL, PhysicalLifeFits] using h1)
        az.1 az.2 (by simpa [hM, PhysicalLifeFits] using h2))
  | some az =>
    cases hM : m p with
    | none =>
      exact False.elim (hlnone_some (by simpa [hM, PhysicalLifeFits] using h2)
        az.1 az.2 (by simpa [hL, PhysicalLifeFits] using h1))
    | some bz =>
      simp only [hL] at h1
      simp only [hM] at h2
      have ha : az.1 = bz.1 := by
        have hb := (h1.2.2.2 az.1).2.2.2.1.mpr rfl
        exact ((h2.2.2.2 az.1).2.2.2.1.mp hb).symm
      have hz : az.2 = bz.2 := by
        have he := (h1.2.2.2 az.2).2.2.2.2.mpr rfl
        exact ((h2.2.2.2 az.2).2.2.2.2.mp he).symm
      exact congrArg some (Prod.ext ha hz)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Every genuinely nonzero fixed-zeta/reversed-K ROOT trace has exactly one
bounded complete active/pending/ghost lifespan profile. Initial and terminal
vacua and all chronological conditions are conclusions of the actual root.
This proves the one-way set-clock readout only, not residues or weighted
surjectivity from frozen independent paths. -/
theorem memory_source_root_unique_lifespan_readout
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hR : 0 < R)
    (hnum : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig Knu zeta theta k R hR w
    ∃! life : (g : BG) → BP g → Option (ℕ × ℕ),
      ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        k (2*R) H g) (2*R+1) (life g) := by
  dsimp only
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod J ell m cap
    patterns q rho Vsmall Vbig Knu zeta theta k R hR w
  have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod J ell m cap
    patterns q rho Vsmall Vbig Knu zeta theta k R hR w
  have hex : ∀ g, ∃ l : BP g → Option (ℕ × ℕ),
      PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
        k (2*R) H g) (2*R+1) l := by
    intro g
    exact physical_actual_BIG_lifespans SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H hnum hVac g
  let life := fun g => Classical.choose (hex g)
  have hfits : ∀ g, PhysicalLifeFits (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      k (2*R) H g) (2*R+1) (life g) := fun g => Classical.choose_spec (hex g)
  refine ⟨life, hfits, ?_⟩
  intro other hother
  funext g
  exact memory_physical_life_fits_unique _ _ _ _ (hother g) (hfits g)
end Green64FullPhysicalE

end

end

