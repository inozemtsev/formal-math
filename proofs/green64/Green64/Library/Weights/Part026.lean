module

public import Green64.Library.Correlation.Part006
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Weights.B26CleanSmallCoherentPairing

@[expose] public section

/-!
# Weights / Part026

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26SmallPermutedConditioning -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (M : ℕ)

/-- A conditional source fibre injects into the SAME original SMALL
physical edge's allowed target list with zero displacement.
No independent sampling of unshared marks is introduced. -/
theorem source_original_small_permuted_fibre_card434
    (shared : Finset (Fin M))
    (sigma : Equiv.Perm (Fin M))
    (d : ↥shared → P)
    (y : Green64SmallHaar.SmallTorus modulus) :
    (memoryOriginalSmallPermutedFibre modulus M shared sigma d y).card ≤
      (Green64SmallHaar.omega modulus y - shared.card).descFactorial
        (Green64SmallHaar.unsharedSlots M shared) := by
  let T := memoryOriginalSmallPermutedFibre modulus M shared sigma d y
  by_cases he : T.Nonempty
  · obtain ⟨x0,hx0⟩ := he
    have h0 : Green64SmallHaar.residues modulus M x0 = y ∧
        ∀ i : ↥shared, Green64SmallHaar.marks modulus M x0 (sigma i.val) = d i := by
      have hh : memoryOriginalSmallSharedLabels modulus M shared sigma x0 = d ∧
          Green64SmallHaar.residues modulus M x0 = y :=
        by simpa only [T,memoryOriginalSmallPermutedFibre,memoryFiniteConditionalFibre,
          Finset.mem_filter,Finset.mem_univ,true_and] using hx0
      exact ⟨hh.2,fun i => congrFun hh.1 i⟩
    let C := Green64SmallHaar.memorySmallAllowed modulus M shared 0
      sigma sigma x0
    have hsub : T ⊆ C := by
      intro x hx
      have h1 : Green64SmallHaar.residues modulus M x = y ∧
          ∀ i : ↥shared, Green64SmallHaar.marks modulus M x (sigma i.val) = d i := by
        have hh : memoryOriginalSmallSharedLabels modulus M shared sigma x = d ∧
            Green64SmallHaar.residues modulus M x = y :=
          by simpa only [T,memoryOriginalSmallPermutedFibre,memoryFiniteConditionalFibre,
            Finset.mem_filter,Finset.mem_univ,true_and] using hx
        exact ⟨hh.2,fun i => congrFun hh.1 i⟩
      change x ∈ Green64SmallHaar.memorySmallAllowed modulus M shared
        0 sigma sigma x0
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · rw [h1.1, h0.1]
        exact (Green64SmallHaar.translate_zero modulus y).symm
      · intro j hj
        have h01 := h0.2 ⟨j,hj⟩
        have h11 := h1.2 ⟨j,hj⟩
        exact h01.trans h11.symm
    have ha : Green64SmallHaar.edgeAllowedPerm modulus M shared 0
        sigma sigma x0 x0 := by
      constructor
      · exact (Green64SmallHaar.translate_zero modulus _).symm
      · intro j hj
        rfl
    have hcount := Green64SmallHaar.memory_small_allowed_card
      modulus M shared 0 sigma sigma x0 x0 ha
    exact (Finset.card_le_card hsub).trans
       (by simpa only [h0.1] using hcount)
  · have hh : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change T.card ≤ _
    rw [hh, Finset.card_empty]
    exact Nat.zero_le _

/-- For every actual physical shared-label tuple d and Haar residue
y, the squared conditioning map costs at most the fixed source
factor ell!/(V^ell*(1-q)^(ell+1)), INDEPENDENT of J. -/
theorem source_original_small_permuted_fibre_weight434
    (J ell : ℕ) (q V : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hV : 0 < V)
    (shared : Finset (Fin (J+ell))) (hshared : shared.card = J)
    (sigma : Equiv.Perm (Fin (J+ell)))
    (d : ↥shared → P) (y : Green64SmallHaar.SmallTorus modulus) :
    memorySmallConditionalRatio modulus J ell q V y *
      ((memoryOriginalSmallPermutedFibre modulus (J+ell) shared sigma d y).card : ℝ) ≤
    (ell.factorial : ℝ) / ((1-q)^(ell+1)*V^ell) := by
  let T := memoryOriginalSmallPermutedFibre modulus (J+ell) shared sigma d y
  have hrest : Green64SmallHaar.unsharedSlots (J+ell) shared = ell := by
    unfold Green64SmallHaar.unsharedSlots
    rw [hshared]
    omega
  have hn := source_original_small_permuted_fibre_card434 modulus
      (J+ell) shared sigma d y
  rw [hshared, hrest] at hn
  have hh : (T.card : ℝ) ≤
      ((Green64SmallHaar.omega modulus y - J).descFactorial ell : ℝ) := by
    exact_mod_cast hn
  have hpos : 0 ≤ q ^ (Green64SmallHaar.omega modulus y-(J+ell)) :=
    pow_nonneg hq.le _
  have hden : 0 ≤ V^ell := pow_nonneg hV.le _
  have hbound : (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
      (T.card : ℝ)) / V^ell ≤
    (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
      ((Green64SmallHaar.omega modulus y-J).descFactorial ell : ℝ)) /
      V^ell := by
    apply div_le_div_of_nonneg_right _ hden
    exact mul_le_mul_of_nonneg_left hh hpos
  by_cases he : T.Nonempty
  · obtain ⟨x,hx⟩ := he
    have hxres : Green64SmallHaar.residues modulus (J+ell) x = y := by
      have hh : memoryOriginalSmallSharedLabels modulus (J+ell) shared sigma x = d ∧
          Green64SmallHaar.residues modulus (J+ell) x = y := by
        simpa only [T,memoryOriginalSmallPermutedFibre,memoryFiniteConditionalFibre,
          Finset.mem_filter,Finset.mem_univ,true_and] using hx
      exact hh.2
    have hz : J+ell ≤ Green64SmallHaar.omega modulus y := by
      rw [← hxres]
      exact Green64SmallHaar.omega_ge_M modulus (J+ell) x
    have hmain := memory_small_conditioning_envelope q V
        hq hq1 hV J ell (Green64SmallHaar.omega modulus y) hz
    dsimp only [memorySmallConditionalRatio]
    change (q ^ (Green64SmallHaar.omega modulus y - (J+ell)) / V^ell) *
       (T.card : ℝ) ≤ _
    calc
      _ = (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
         (T.card:ℝ)) / V^ell := by ring
      _ ≤ _ := hbound
      _ ≤ _ := hmain
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change memorySmallConditionalRatio modulus J ell q V y *
      (T.card:ℝ) ≤ _
    rw [hT]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalB26SmallGroupHalfEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable (J ell : ℕ)

theorem source_original_small_group_permuted_fibre_card434
    (shared : SG → Finset (Fin (J+ell)))
    (sigma : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    (memoryOriginalSmallGroupPermutedFibre SP smallMod (J+ell)
      shared sigma d y).card =
    ∏ g : SG,(memoryOriginalSmallPermutedFibre (smallMod g)
      (J+ell) (shared g) (sigma g) (d g) (y g)).card := by
  classical
  have heq : memoryOriginalSmallGroupPermutedFibre SP smallMod (J+ell)
      shared sigma d y =
      Fintype.piFinset (fun g => memoryOriginalSmallPermutedFibre (smallMod g)
        (J+ell) (shared g) (sigma g) (d g) (y g)) := by
    ext xs
    simp only [memoryOriginalSmallGroupPermutedFibre,
      memoryOriginalSmallPermutedFibre,memoryFiniteConditionalFibre,
      Finset.mem_filter,Finset.mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · rintro ⟨hd,hy⟩ g
      exact ⟨congrFun hd g,congrFun hy g⟩
    · intro h
      exact ⟨funext (fun g => (h g).1),funext (fun g => (h g).2)⟩
  rw [heq]
  exact Fintype.card_piFinset _

theorem source_original_small_group_permuted_fibre_weight434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g,(shared g).card = J)
    (sigma : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    memorySmallGroupConditionalRatio SP smallMod J ell q Vs y *
      ((memoryOriginalSmallGroupPermutedFibre SP smallMod (J+ell)
        shared sigma d y).card : ℝ) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs := by
  rw [source_original_small_group_permuted_fibre_card434]
  simp only [Nat.cast_prod]
  unfold memorySmallGroupConditionalRatio memorySmallGroupConditioningConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro g _
    apply mul_nonneg _ (Nat.cast_nonneg _)
    unfold memorySmallConditionalRatio
    exact div_nonneg (pow_nonneg hq.le _) (pow_nonneg (hVs g).le _)
  · intro g _
    exact source_original_small_permuted_fibre_weight434
      (smallMod g) J ell q (Vs g) hq hq1 (hVs g)
      (shared g) (hshared g) (sigma g) (d g) (y g)

/-- Squared energy of the actual independently permuted SMALL P_d.
The exact fibre multiplicity is paid once; the constant is independent
of J, the residue modulus and the number of available prime labels. -/
theorem source_original_small_permuted_half_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g,(shared g).card = J)
    (sigma : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (w : Green64SmallHaar.GroupState SP smallMod (J+ell) → ℂ) :
    (∑ d : (g : SG) → ↥(shared g) → SP g,
      ∑ y : Green64SmallHaar.GroupTorus SP smallMod,
        ‖memoryOriginalSmallPermutedHalfMap SP smallMod J ell
          q Vs shared sigma d y w‖^2) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      ∑ xs : Green64SmallHaar.GroupState SP smallMod (J+ell),‖w xs‖^2 := by
  classical
  let a := memorySmallGroupConditionalRatio SP smallMod J ell q Vs
  let C := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  have ha (y : Green64SmallHaar.GroupTorus SP smallMod) : 0 ≤ a y := by
    apply Finset.prod_nonneg
    intro g _
    dsimp [memorySmallConditionalRatio]
    exact div_nonneg (pow_nonneg hq.le _) (pow_nonneg (hVs g).le _)
  have hC : 0 ≤ C := by
    apply Finset.prod_nonneg
    intro g _
    have hv := hVs g
    have hq' : 0 < 1-q := by linarith
    positivity
  have hh := memory_finite_conditioning_norm_sq
    (memoryOriginalSmallGroupSharedLabels SP smallMod (J+ell) shared sigma)
    (memoryOriginalSmallGroupResidue SP smallMod (J+ell))
    a ha C hC
    (fun d y => source_original_small_group_permuted_fibre_weight434
      SP smallMod J ell q hq hq1 Vs hVs shared hshared sigma d y) w
  have heq (d : (g : SG) → ↥(shared g) → SP g)
      (y : Green64SmallHaar.GroupTorus SP smallMod) :
      ‖memoryOriginalSmallPermutedHalfMap SP smallMod J ell
          q Vs shared sigma d y w‖^2 =
      a y * ‖∑ xs ∈ memoryOriginalSmallGroupPermutedFibre SP smallMod
        (J+ell) shared sigma d y,w xs‖^2 := by
    unfold memoryOriginalSmallPermutedHalfMap
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      memory_original_small_group_endpoint_half_sq SP smallMod J ell q hq.le Vs hVs]
  simpa only [heq,memoryOriginalSmallGroupPermutedFibre,a,C] using hh
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalB26SmallOldEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => Green64SmallHaar.GroupState SP smallMod (J+ell)
local notation "SmallTorus" => Green64SmallHaar.GroupTorus SP smallMod
local notation "SmallPerm" => Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bigMod sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime

theorem source_original_B26_sector_mass_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (a : Active) :
    0 ≤ sourceOriginalB26SectorMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu a := by
  unfold sourceOriginalB26SectorMass434
  apply mul_nonneg
  · unfold Green64SmallHaar.groupStateMass
    exact Finset.prod_nonneg (fun g _ =>
      (Green64SmallHaar.stateMass_positive (smallMod g) (J+ell) (Vs g) (hVs g)).le)
  · exact (bigGroupStateMass_positive BP bigMod (J+ell) cap mu hmu _).le

theorem source_original_B26_small_shared_card434 (g : SG) :
    (sourceSmallShared J ell g).card = J := by
  let e : Fin J ≃ ↥(sourceSmallShared J ell g) :=
    { toFun := fun j => ⟨⟨j.val,by omega⟩,by simp [sourceSmallShared,j.isLt]⟩
      invFun := fun j => ⟨j.val.val,by
        simpa only [sourceSmallShared,Finset.mem_filter,Finset.mem_univ,true_and]
          using j.property⟩
      left_inv := by intro j;rfl
      right_inv := by intro j;apply Subtype.ext;rfl }
  simpa using (Fintype.card_congr e).symm

/-- Actual P_d energy in one ordered OLD sector, with every original
SMALL Haar, BIG harmonic and Fock factor. The complete OLD residue
tuple stays a variable and no endpoint test is made independent. -/
theorem source_original_B26_SMALL_OLD_ENERGY434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (ss : SmallPerm) (U : Small → Active → Old → ℂ) :
    (∑ d : Shared,∑ a : Active,∑ r : Torus,
      sourceOriginalB26SectorMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu a *
      ‖sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a r‖^2) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      ∑ a : Active,∑ xs : Small,∑ t : Old,
        sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime Vs mu a * ‖U xs a t‖^2 := by
  classical
  let mass := sourceOriginalB26SectorMass434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs mu
  let C := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  have hmass := source_original_B26_sector_mass_nonneg434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs hVs mu hmu
  calc
    _ = ∑ a : Active,∑ t : Old,mass a *
        (∑ d : Shared,∑ y : SmallTorus,
          ‖sourceOriginalB26SmallLift434 SP smallMod BP bigMod
            J ell sizes prime q Vs ss d U a (y,t)‖^2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Fintype.sum_prod_type,Finset.mul_sum]
      calc
        _ = ∑ d : Shared,∑ t : Old,∑ y : SmallTorus,
            mass a * ‖sourceOriginalB26SmallLift434 SP smallMod BP bigMod
              J ell sizes prime q Vs ss d U a (y,t)‖^2 := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ ≤ ∑ a : Active,∑ t : Old,mass a *
        (C * ∑ xs : Small,‖U xs a t‖^2) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (hmass a)
      exact source_original_small_permuted_half_energy434 SP smallMod J ell
        q hq hq1 Vs hVs (sourceSmallShared J ell)
        (source_original_B26_small_shared_card434 J ell) ss (fun xs => U xs a t)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [mass,C]
      ring
end Green64FullPhysicalE

end

end

