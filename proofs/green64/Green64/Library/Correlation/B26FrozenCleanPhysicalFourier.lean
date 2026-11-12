module

public import Green64.Library.Correlation.MemoryFullChainRhoInvariant
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part002
public import Green64.Library.Analysis.Estimates.Part003

@[expose] public section

/-!
# Correlation / B26FrozenCleanPhysicalFourier

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26FrozenCleanPhysicalFourier -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem character_sum_pair434
    {G : Type} [Fintype G] [AddCommGroup G]
    (psi phi : AddChar G ℂ) :
    (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) =
      if psi = phi then (Fintype.card G : ℂ) else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole psi phi
  have h' : (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) /
      (Fintype.card G : ℂ) = if psi = phi then 1 else 0 := by
    simpa only [RCLike.wInner_cWeight_eq_expect,
      Fintype.expect_eq_sum_div_card, RCLike.inner_apply, mul_comm] using h
  have hn : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh := (div_eq_iff hn).mp h'
  split_ifs at hh ⊢ <;> simpa using hh

private theorem fourier_synthesis_pair434
    {G : Type} [Fintype G] [AddCommGroup G]
    (a b : AddChar G ℂ → ℂ) :
    (∑ r : G,
      (starRingEnd ℂ) (∑ psi : AddChar G ℂ, a psi * psi r) *
        (∑ phi : AddChar G ℂ, b phi * phi r)) =
    (Fintype.card G : ℂ) *
      ∑ psi : AddChar G ℂ, (starRingEnd ℂ) (a psi) * b psi := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ phi : AddChar G ℂ, ∑ psi : AddChar G ℂ,
        ((starRingEnd ℂ) (a psi) * b phi) *
          (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro phi _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro psi _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      simp_rw [character_sum_pair434]
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

private theorem fourier_synthesis_energy434
    {G : Type} [Fintype G] [AddCommGroup G]
    (a : AddChar G ℂ → ℂ) :
    (∑ r : G, ‖∑ psi : AddChar G ℂ, a psi * psi r‖^2) =
    (Fintype.card G : ℝ) * ∑ psi : AddChar G ℂ, ‖a psi‖^2 := by
  have h := fourier_synthesis_pair434 a a
  simp only [RCLike.conj_mul] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

private theorem full_fourier_energy434
    {G : Type} [Fintype G] [AddCommGroup G] (f : G → ℂ) :
    (∑ r : G, ‖f r‖^2) =
    (Fintype.card G : ℝ) *
      ∑ psi : AddChar G ℂ, ‖(AddChar.complexBasis G).repr f psi‖^2 := by
  have he (r : G) :
      f r = ∑ psi : AddChar G ℂ,
        (AddChar.complexBasis G).repr f psi * psi r := by
    have h := congrFun ((AddChar.complexBasis G).sum_repr f) r
    simpa only [AddChar.complexBasis_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  calc
    _ = ∑ r : G, ‖∑ psi : AddChar G ℂ,
        (AddChar.complexBasis G).repr f psi * psi r‖^2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [he]
    _ = _ := fourier_synthesis_energy434 _

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

abbrev SourceOriginalB26Active434 := (g : BG) → Fin (J+ell) → BP g

local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime

/-- Actual ordered BIG active/Fock state in one original frozen sector.
Each OLD occurrence retains its own residue, including repeated primes. -/
def sourceOriginalB26FrozenBigState434
    (a : Active)
    (r : (g : BG) → (i : Fin (sizes g)) → ZMod (bigMod g (prime g i))) :
    BigGroupState BP bigMod (J+ell) cap :=
  fun g => (a g, ⟨⟨sizes g, by have h := hsizes g; omega⟩,
    fun i => ⟨prime g i, r g i⟩⟩)

/-- The unique no-store/no-promotion choice in the ORIGINAL choice type. -/
def sourceOriginalB26EmptyCleanChoice434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (M B : ℕ) (x : BigState modulus M B) :
    BigEdgeChoice modulus M B x := by
  refine (∅, ⟨∅, ?_⟩)
  refine ⟨?_, ?_⟩
  · intro i
    exact (Finset.notMem_empty _ i.property).elim
  · intro i j h
    exact (Finset.notMem_empty _ i.property).elim

/-- Exact original source divisor after freezing the SMALL shared product.
The BIG part still reads the independently permuted source slots and aux. -/
def sourceOriginalB26FrozenD434
    (dsmall : ℕ) (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (a : Active) (sigma : BigGroupPerm (BG := BG) (J+ell)) : ℕ :=
  dsmall * ∏ g : BG,
    (∏ i ∈ sourceBigShared J ell m pat g, bigMod g (a g (sigma g i))) *
    (∏ j : ↥(pat.free g), bigMod g (aux g j))

/-- This is the actual source auxiliary/active ban, on both endpoints. -/
def sourceOriginalB26FrozenAuxBan434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (a b : Active) : Prop :=
  ∀ (g : BG) (j : ↥(pat.free g)) (i : Fin (J+ell)),
    aux g j ≠ a g i ∧ aux g j ≠ b g i

/-- Actual original BIG legal-filtered coefficient at rho=1, the algebraic
reference after absorbing the proved OLD endpoint multipliers.
Neither the oriented legality nor the source coefficient is replaced here. -/
def sourceOriginalB26FrozenPhysicalCoefficient434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (pat : SourcePattern BG J m)
    (a b : Active) (sigma tau : BigGroupPerm (BG := BG) (J+ell))
    (D : ℕ) (step : ℤ) (r : Torus) : ℂ :=
  ∏ g : BG,
    let x := sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2 g
    let c := sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell) (cap g) x
    if OrientedBigEdgeLegal (bigMod g) (J+ell) (cap g)
        x (b g) (sourceBigShared J ell m pat g) (sigma g) (tau g) D step c
    then orientedBigBranchCoefficient (bigMod g) (J+ell) (cap g)
        (mu g) (V g) 1 x (b g) (sourceBigShared J ell m pat g)
        (sigma g) (tau g) step c
    else 0

/-- The precise shared-copy/fresh-prime coefficient derived in B26. -/
def sourceOriginalB26FrozenFreshLaw434
    (mu : (g : BG) → BP g → ℝ) (pat : SourcePattern BG J m)
    (a b : Active) (sigma tau : BigGroupPerm (BG := BG) (J+ell)) : ℂ :=
  ∏ g : BG, ∏ i : Fin (J+ell),
    if (tau g).symm i ∈ sourceBigShared J ell m pat g then
      (if b g i = a g (sigma g ((tau g).symm i)) then 1 else 0)
    else (mu g (b g i) : ℂ)

/-- Original physical CLEAN coefficient is independent of ALL frozen residue
coordinates after OLD endpoint factors are removed. This uses the previously
proved B26 target law, without assuming independent physical outputs. -/
theorem source_original_B26_FROZEN_PHYSICAL_coefficient434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (pat : SourcePattern BG J m)
    (a b : Active) (sigma tau : BigGroupPerm (BG := BG) (J+ell))
    (D : ℕ) (step : ℤ) (r : Torus) :
    sourceOriginalB26FrozenPhysicalCoefficient434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime mu V pat a b sigma tau D step r =
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau := by
  unfold sourceOriginalB26FrozenPhysicalCoefficient434 sourceOriginalB26FrozenFreshLaw434
  apply Finset.prod_congr rfl
  intro g _
  dsimp only
  rw [memory_original_clean_big_target_indicator_factors
    (bigMod g) (J+ell) (cap g) (mu g) (V g) 1 _ _ _ _ _ _ _ _
    (by rfl) (by rfl)]
  simp only [Complex.ofReal_one, one_pow, one_mul, sourceOriginalB26FrozenBigState434]
  rfl

/-- No dummy SMALL state is used: specializing dsmall to the actual source
SMALL shared product gives exactly sourceOrientedPhysicalD. -/
theorem source_original_B26_FROZEN_D_from_original434
    (xs : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (a : Active) (r : Torus)
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (sigmaB : BigGroupPerm (BG := BG) (J+ell))
    (sigmaS : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap pat aux
      (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2)
      sigmaB sigmaS =
    sourceOriginalB26FrozenD434 BP bigMod J ell m
      (∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
        smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell) (xs g) (sigmaS g i)))
      pat aux a sigmaB := rfl

/-- The actual output pending multiset is the frozen sector at r+step.
The full indexed OLD multiplicity survives the map to the symmetric carrier. -/
theorem source_original_B26_FROZEN_pending_output434
    (a : Active) (r : Torus)
    (sigma : BigGroupPerm (BG := BG) (J+ell)) (step : ℤ) (g : BG) :
    let x := sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2 g
    physicalPendingMultiset (bigMod g) (J+ell) (cap g) x (sigma g) step
      (sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell) (cap g) x) =
    Green64Fock.fockMultiset
      ((sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a
        (fun g i => r.2 g i + (step : ZMod (bigMod g (prime g i)))) g).2) := by
  dsimp only
  rw [memory_original_clean_pending_exact (bigMod g) (J+ell) (cap g)
    _ _ _ _ (by rfl) (by rfl)]
  simp [sourceOriginalB26FrozenBigState434, Green64Fock.fockMultiset,
    Green64PhysicalEdge.translateAtom, List.map_ofFn, Function.comp_def]

/-- The original physical mass of this frozen ordered sector, including every
1/j!, is constant in its residue coordinates. No flat Fock mass is substituted. -/
theorem source_original_B26_FROZEN_Fock_mass434
    (mu : (g : BG) → BP g → ℝ) (a : Active) (r s : Torus) :
    (∏ g : BG, bigStateMass (bigMod g) (J+ell) (cap g) (mu g)
      (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2 g)) =
    (∏ g : BG, bigStateMass (bigMod g) (J+ell) (cap g) (mu g)
      (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a s.2 g)) := by
  rfl

/-- All original Nu, auxiliary and independently sampled BIG endpoint
permutations in ONE coherent index. It has no free history weights. -/
abbrev SourceOriginalB26FrozenFrame434 :=
  Σ nu : Nu, SourceBigAux BP J m (patterns nu) ×
    BigGroupPerm (BG := BG) (J+ell) × BigGroupPerm (BG := BG) (J+ell)

def sourceOriginalB26ModeAngle434 (psi : AddChar Torus ℂ) : ℝ :=
  Classical.choose (memory_frozen_residue_character_real_angle SP smallMod
    BP bigMod sizes prime psi)

private theorem mode_angle_spec434 (psi : AddChar Torus ℂ) (step : ℤ) :
    psi (memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step) =
      Complex.exp (((step : ℝ) *
        sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi : ℝ) *
        Complex.I) :=
  Classical.choose_spec (memory_frozen_residue_character_real_angle
    SP smallMod BP bigMod sizes prime psi) step

/-- Fourier translation changes the ONE original return frequency by a fixed
real number depending only on the frozen sector and mode. K, zeta, D and the
orientation remain the source ones, including genuinely complex K. -/
theorem source_original_B26_FROZEN_scalar_frequency434
    (psi : AddChar Torus ℂ) (K : ℂ) (zeta theta : ℝ) (D : ℕ) (o k : ℤ) :
    originalEdgeScalar K zeta theta D o k *
      psi (memoryFrozenResidueShift SP smallMod BP bigMod sizes prime
        (o*k*(D : ℤ))) =
    originalEdgeScalar K zeta
      (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
        (2*Real.pi)) D o k := by
  rw [mode_angle_spec434 SP smallMod BP bigMod sizes prime psi]
  unfold originalEdgeScalar originalReturnPhase
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  <;> ring


local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns

/-- One actual conditioned CLEAN term, still expressed using ORIGINAL
oriented BIG legality and branch coefficients. Only SMALL shared labels
and ordered OLD prime labels have been frozen. Global birth distinctness
is not imposed in this local unmarked CLEAN object. -/
def sourceOriginalB26FrozenPhysicalWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  let step := o*k*(D : ℤ)
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenPhysicalCoefficient434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime mu V pat a b sigma tau D step r *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

/-- The derived BIG coefficient. Its source auxiliary mass, both endpoint
permutation masses, true shared-copy law, endpoint auxiliary ban, complex
K, Mellin phase and oriented return phase are all retained. -/
def sourceOriginalB26FrozenBigWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

private theorem frozen_weight_eq434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b =
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b := by
  unfold sourceOriginalB26FrozenPhysicalWeight434 sourceOriginalB26FrozenBigWeight434
  dsimp only
  rw [source_original_B26_FROZEN_PHYSICAL_coefficient434]

private theorem frozen_weight_frequency434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) (psi : AddChar Torus ℂ) :
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b *
      psi (memoryFrozenResidueShift SP smallMod BP bigMod sizes prime
        (o*k*(sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
          (patterns h.1) h.2.1 a h.2.2.1 : ℤ))) =
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta
      (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
        (2*Real.pi)) o k a h b := by
  unfold sourceOriginalB26FrozenBigWeight434
  dsimp only
  split_ifs
  · rw [mul_assoc, source_original_B26_FROZEN_scalar_frequency434
      SP smallMod BP bigMod sizes prime psi]
  · simp

/-- The conditioned physical CLEAN operator; the coherent sum over all
original Nu, aux and independent sigma/tau is inside the operator. -/
def sourceOriginalB26FrozenPhysicalOp434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Active → Torus → ℂ) (a : Active) (r : Torus) : ℂ :=
  ∑ h : Frame, ∑ b : Active,
    sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b *
    F b (r + memoryFrozenResidueShift SP smallMod BP bigMod sizes prime
      (o*k*(sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
        (patterns h.1) h.2.1 a h.2.2.1 : ℤ)))

/-- The true coherent BIG block, with the SAME sum of original signed Knu.
No arbitrary small-matrix or per-history norm assumption is introduced. -/
def sourceOriginalB26FrozenBigBlock434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : Active → ℂ) (a : Active) : ℂ :=
  ∑ h : Frame, ∑ b : Active,
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b * f b

/-- Exact full Fourier decomposition of the physical conditioned CLEAN
operator. Crucially, the FULL signed source sum remains within each block.
Repeated OLD prime occurrences have independent Fourier coordinates. -/
theorem source_original_B26_FROZEN_COHERENT_FOURIER434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Active → Torus → ℂ) (a : Active) (r : Torus) :
    sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k F a r =
    ∑ psi : AddChar Torus ℂ,
      sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
        dsmall zeta
        (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
          (2*Real.pi)) o k
        (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a * psi r := by
  unfold sourceOriginalB26FrozenPhysicalOp434
  simp_rw [frozen_weight_eq434 SP smallMod BP bigMod J ell m cap sizes hsizes prime]
  simp_rw [memory_frozen_full_residue_fourier_shift_formula SP smallMod BP bigMod
    sizes prime, Finset.mul_sum]
  calc
    _ = ∑ h : Frame, ∑ b : Active, ∑ psi : AddChar Torus ℂ,
        (sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
          mu V K dsmall zeta
          (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
            (2*Real.pi)) o k a h b *
        (AddChar.complexBasis Torus).repr (F b) psi) * psi r := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro psi _
      rw [← frozen_weight_frequency434 SP smallMod BP bigMod J ell m
        sizes prime patterns mu V K dsmall zeta theta o k a h b psi]
      ring
    _ = _ := by
      unfold sourceOriginalB26FrozenBigBlock434
      simp only [Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_comm]



/-- Actual SMALL Haar mass times original BIG/Fock source mass of the
ordered frozen sector. Every original factorial and prime weight stays. -/
def sourceOriginalB26FrozenPhysicalMass434
    (mu : (g : BG) → BP g → ℝ) (a : Active) (r : Torus) : ℝ :=
  Green64SmallHaar.groupHaarMass SP smallMod *
    ∏ g : BG, bigStateMass (bigMod g) (J+ell) (cap g) (mu g)
      (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2 g)

private theorem frozen_mass_constant434
    (mu : (g : BG) → BP g → ℝ) (a : Active) (r s : Torus) :
    sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime mu a r =
    sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime mu a s := rfl

/-- Parseval for the INPUT with the ORIGINAL physical frozen-sector mass.
The cardinal factor includes counting OLD residues, not an invented Haar
normalization on the pending Fock component. -/
theorem source_original_B26_FROZEN_PHYSICAL_INPUT_ENERGY434
    (mu : (g : BG) → BP g → ℝ) (F : Active → Torus → ℂ) :
    (∑ a : Active, ∑ r : Torus,
      sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime mu a r * ‖F a r‖^2) =
    (Fintype.card Torus : ℝ) *
      ∑ psi : AddChar Torus ℂ, ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
          ‖(AddChar.complexBasis Torus).repr (F a) psi‖^2 := by
  calc
    _ = ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        (∑ r : Torus, ‖F a r‖^2) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [frozen_mass_constant434 SP smallMod BP bigMod J ell cap
        sizes hsizes prime mu a r 0]
    _ = ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        ((Fintype.card Torus : ℝ) *
          ∑ psi : AddChar Torus ℂ,
            ‖(AddChar.complexBasis Torus).repr (F a) psi‖^2) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact full_fourier_energy434 (F a)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro psi _
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Exact OUTPUT physical energy of the coherent original CLEAN block.
All Nu/aux/permutation cross terms are retained INSIDE each square.
Together with INPUT_ENERGY, this proves there is no additional
number-of-modes loss. It supplies no arithmetic estimate on the blocks. -/
theorem source_original_B26_FROZEN_COHERENT_PHYSICAL_ENERGY434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Active → Torus → ℂ) :
    (∑ a : Active, ∑ r : Torus,
      sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime mu a r *
      ‖sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k
        F a r‖^2) =
    (Fintype.card Torus : ℝ) *
      ∑ psi : AddChar Torus ℂ, ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        ‖sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
          dsmall zeta
          (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
            (2*Real.pi)) o k
          (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a‖^2 := by
  calc
    _ = ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        (∑ r : Torus,
          ‖sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
            J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k
            F a r‖^2) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [frozen_mass_constant434 SP smallMod BP bigMod J ell cap
        sizes hsizes prime mu a r 0]
    _ = ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        ((Fintype.card Torus : ℝ) *
          ∑ psi : AddChar Torus ℂ,
            ‖sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
              dsmall zeta
              (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
                (2*Real.pi)) o k
              (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a‖^2) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp_rw [source_original_B26_FROZEN_COHERENT_FOURIER434]
      exact fourier_synthesis_energy434 _
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro psi _
      apply Finset.sum_congr rfl
      intro a _
      ring



/-- The SMALL divisor contributes precisely the ORIGINAL oriented Mellin
factor. This scalar is not a counterweight and does not change Knu. -/
def sourceOriginalB26SmallMellin434 (dsmall : ℕ) (zeta : ℝ) (o : ℤ) : ℂ :=
  originalOrientedKernel 1 zeta dsmall o

private theorem positive_nat_log_mul434 (d B : ℕ) (hd : 0 < d) (hB : 0 < B) :
    Complex.log ((d*B : ℕ) : ℂ) =
      Complex.log (d : ℂ) + Complex.log (B : ℂ) := by
  have hr : Real.log ((d*B : ℕ) : ℝ) =
      Real.log (d : ℝ) + Real.log (B : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hB.ne')]
  simpa only [Complex.ofReal_add, Complex.natCast_log] using
    congrArg (fun t : ℝ => (t : ℂ)) hr

private theorem scalar_small_divisor434
    (K : ℂ) (zeta theta : ℝ) (d B : ℕ) (hd : 0 < d) (hB : 0 < B) (o k : ℤ) :
    originalEdgeScalar K zeta theta (d*B) o k =
      sourceOriginalB26SmallMellin434 d zeta o *
      originalEdgeScalar K zeta ((k : ℝ)*(d : ℝ)*theta) B o 1 := by
  have he :
      Complex.exp (Complex.I * (zeta : ℂ) * Complex.log ((d*B : ℕ) : ℂ)) =
      Complex.exp (Complex.I * (zeta : ℂ) * Complex.log (d : ℂ)) *
        Complex.exp (Complex.I * (zeta : ℂ) * Complex.log (B : ℂ)) := by
    rw [positive_nat_log_mul434 d B hd hB, mul_add, Complex.exp_add]
  have hK : originalOrientedKernel K zeta (d*B) o =
      sourceOriginalB26SmallMellin434 d zeta o * originalOrientedKernel K zeta B o := by
    unfold sourceOriginalB26SmallMellin434 originalOrientedKernel
    split_ifs <;> simp only [one_mul, he, star_mul] <;> ring
  have hphase : originalReturnPhase theta o k (d*B) =
      originalReturnPhase ((k : ℝ)*(d : ℝ)*theta) o 1 B := by
    unfold originalReturnPhase
    congr 1
    push_cast
    ring
  unfold originalEdgeScalar
  rw [hK, hphase]
  ring

theorem source_original_B26_SMALL_MELLIN_norm_one434
    (dsmall : ℕ) (zeta : ℝ) (o : ℤ) :
    ‖sourceOriginalB26SmallMellin434 dsmall zeta o‖ = 1 := by
  have he : ‖Complex.exp
      (Complex.I * (zeta : ℂ) * Complex.log (dsmall : ℂ))‖ = 1 := by
    have him : (Complex.log (dsmall : ℂ)).im = 0 := by
      rw [← Complex.natCast_log]
      rfl
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, him]
  unfold sourceOriginalB26SmallMellin434 originalOrientedKernel
  split_ifs <;> simpa only [one_mul, norm_star] using he

private theorem frozen_big_divisor_positive434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (a : Active) (sigma : BigGroupPerm (BG := BG) (J+ell)) :
    0 < sourceOriginalB26FrozenD434 BP bigMod J ell m 1 pat aux a sigma := by
  unfold sourceOriginalB26FrozenD434
  apply mul_pos (by decide)
  apply Finset.prod_pos
  intro g _
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  · apply Finset.prod_pos
    intro j _
    exact Nat.pos_of_ne_zero (NeZero.ne _)

private theorem frozen_big_weight_small_factor434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (hdsmall : 0 < dsmall) (zeta theta : ℝ) (o k : ℤ) (hk : k ≠ 0)
    (a : Active) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b =
    sourceOriginalB26SmallMellin434 dsmall zeta o *
      sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
        mu V K 1 zeta ((k : ℝ)*(dsmall : ℝ)*theta) o 1 a h b := by
  have hB := frozen_big_divisor_positive434 BP bigMod J ell m
    (patterns h.1) h.2.1 a h.2.2.1
  have hD : sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
        (patterns h.1) h.2.1 a h.2.2.1 =
      dsmall * sourceOriginalB26FrozenD434 BP bigMod J ell m 1
        (patterns h.1) h.2.1 a h.2.2.1 := by
    simp only [sourceOriginalB26FrozenD434, one_mul]
  simp only [sourceOriginalB26FrozenBigWeight434, hk, one_ne_zero, true_and]
  split_ifs with hleft hright hright
  · rw [hD, scalar_small_divisor434 _ _ _ _ _ hdsmall hB]
    ring
  · exfalso
    exact hright ⟨hleft.1, by norm_num, hleft.2.2⟩
  · exfalso
    exact hleft ⟨hright.1, hk, hright.2.2⟩
  · rw [mul_zero]

/-- The actual coherent BIG block after freezing SMALL data equals its
BIG-divisor-only version at ONE common rescaled frequency, up to the
original unit Mellin factor. Auxiliary bans and actual mu remain;
this is not yet their comparison with the harmonic ideal operator. -/
theorem source_original_B26_FROZEN_BIG_DIVISOR_REDUCTION434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (hdsmall : 0 < dsmall) (zeta theta : ℝ) (o k : ℤ) (hk : k ≠ 0)
    (f : Active → ℂ) (a : Active) :
    sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k f a =
    sourceOriginalB26SmallMellin434 dsmall zeta o *
      sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns
        mu V K 1 zeta ((k : ℝ)*(dsmall : ℝ)*theta) o 1 f a := by
  unfold sourceOriginalB26FrozenBigBlock434
  simp_rw [frozen_big_weight_small_factor434 BP bigMod J ell m patterns
    mu V K dsmall hdsmall zeta theta o k hk]
  simp only [Finset.mul_sum, mul_assoc]

/-- Physical coherent CLEAN output energy is exactly the sum of genuine
BIG-divisor blocks at rescaled frequencies. SMALL/OLD torus size produces
the SAME factor as INPUT_ENERGY. No norm estimate, hCross, or cancellation
of canonical signed residuals is assumed or concluded. -/
theorem source_original_B26_FROZEN_PHYSICAL_ENERGY_BIG_DIVISOR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (hdsmall : 0 < dsmall) (zeta theta : ℝ) (o k : ℤ) (hk : k ≠ 0)
    (F : Active → Torus → ℂ) :
    (∑ a : Active, ∑ r : Torus,
      sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime mu a r *
      ‖sourceOriginalB26FrozenPhysicalOp434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k
        F a r‖^2) =
    (Fintype.card Torus : ℝ) *
      ∑ psi : AddChar Torus ℂ, ∑ a : Active,
        sourceOriginalB26FrozenPhysicalMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime mu a 0 *
        ‖sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns mu V K
          1 zeta
          ((k : ℝ)*(dsmall : ℝ)*
            (theta + sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi /
              (2*Real.pi))) o 1
          (fun b => (AddChar.complexBasis Torus).repr (F b) psi) a‖^2 := by
  have h := source_original_B26_FROZEN_COHERENT_PHYSICAL_ENERGY434
    SP smallMod BP bigMod J ell m cap sizes hsizes prime patterns
    mu V K dsmall zeta theta o k F
  simp_rw [source_original_B26_FROZEN_BIG_DIVISOR_REDUCTION434
    BP bigMod J ell m patterns mu V K dsmall hdsmall zeta _ o k hk,
    norm_mul, source_original_B26_SMALL_MELLIN_norm_one434, one_mul] at h
  exact h



/-- The SMALL divisor is read from the actual source marks after its
independently sampled source permutation, exactly as source03 prescribes. -/
def sourceOriginalB26SmallSourceD434
    (xs : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) : ℕ :=
  ∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
    smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell) (xs g) (ss g i))

theorem source_original_B26_ACTUAL_SMALL_D_positive434
    (xs : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    0 < sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss := by
  unfold sourceOriginalB26SmallSourceD434
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- A genuine ORIGINAL source choice with empty stores and promotions,
both independently indexed BIG permutations and both SMALL permutations.
This is an inhabitant of the existing physical source-choice type. -/
def sourceOriginalB26FrozenOriginalChoice434
    (xs ys : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (a : Active) (r : Torus) (h : Frame) (b : Active)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns
      (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2) :=
  ⟨h.1, h.2.1,
    ⟨h.2.2.1, h.2.2.2,
      (fun g => (b g, sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell)
        (cap g) (sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
          sizes hsizes prime a r.2 g))), ys⟩, ss, tt⟩

/-- EXACT link to one literal ORIGINAL CLEAN summand, before SMALL P_d
disintegration: the complete original legality-filtered coefficient
factors into our physical frozen weight and the actual SMALL kernel.
It includes all original bans, both BIG/SMALL permutation masses, moving
D, orientation, complex Knu and OLD empty-choice physical coefficients.
No equality with the full birth-marked Memory chain is asserted. -/
theorem source_original_B26_FROZEN_ORIGINAL_CLEAN_SUMMAND434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (xs ys : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (a : Active) (r : Torus) (h : Frame) (b : Active)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a r.2)
    let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns xs ys a r h b ss tt
    let dsmall := sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss
    let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
      (patterns h.1) h.2.1 a h.2.2.1
    (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z
      then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x z else 0) =
    sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b *
      (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vs
        (sourceSmallShared J ell) (o*k*(D : ℤ)) (fun _ _ => 1) ss tt xs ys := by
  dsimp only
  let xb := sourceOriginalB26FrozenBigState434 BP bigMod J ell cap sizes hsizes prime a r.2
  let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns xs ys a r h b ss tt
  let dsmall := sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
    (patterns h.1) h.2.1 a h.2.2.1
  let step := o*k*(D : ℤ)
  let allowed : Prop := (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
    sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 a b
  let Lg : BG → Prop := fun g =>
    OrientedBigEdgeLegal (bigMod g) (J+ell) (cap g) (xb g) (b g)
      (sourceBigShared J ell m (patterns h.1) g) (h.2.2.1 g) (h.2.2.2 g) D step
      (sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell) (cap g) (xb g))
  let Cg : BG → ℂ := fun g =>
    orientedBigBranchCoefficient (bigMod g) (J+ell) (cap g) (mu g) (V g) 1
      (xb g) (b g) (sourceBigShared J ell m (patterns h.1) g)
      (h.2.2.1 g) (h.2.2.2 g) step
      (sourceOriginalB26EmptyCleanChoice434 (bigMod g) (J+ell) (cap g) (xb g))
  let smallLegal : Prop := Green64SmallHaar.groupEdgeAllowedPerm
    SP smallMod (J+ell) (sourceSmallShared J ell) step ss tt xs ys
  let W : ℂ := (sourceAuxMass BP bigMod J m V (patterns h.1) h.2.1 : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ)
  let P : ℂ := (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ)
  let scalar : ℂ := originalEdgeScalar
    (K h.1 h.2.1 (fun g i => a g (h.2.2.1 g i)) (fun g i => b g (h.2.2.2 g i)))
    zeta theta D o k
  let smallScalar : ℂ := (Green64SmallHaar.groupEdgeScalar SP smallMod
    (J+ell) q Vs (sourceSmallShared J ell) xs ys : ℂ)
  have hleg : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap
      patterns (xs, xb) o k z ↔ allowed ∧ (∀ g, Lg g) ∧ smallLegal := by
    change ((o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 a b ∧
      (∀ g, Lg g) ∧ smallLegal) ↔ allowed ∧ (∀ g, Lg g) ∧ smallLegal
    dsimp only [allowed]
    tauto
  rw [hleg]
  have hcoef : sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q 1 Vs V mu K zeta theta o k (xs, xb) z =
      W*P*(∏ g, Cg g)*(if smallLegal then scalar*smallScalar else 0) := by
    rfl
  have hw : sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b =
      (if allowed then W*(∏ g, if Lg g then Cg g else 0)*scalar else 0) := by
    rfl
  have hsKernel : Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vs
      (sourceSmallShared J ell) step (fun _ _ => 1) ss tt xs ys =
      (if smallLegal then 1*smallScalar else 0) := by
    rfl
  rw [hcoef, hw, hsKernel]
  have hprod : (∏ g : BG, if Lg g then Cg g else 0) =
      if ∀ g : BG, Lg g then ∏ g : BG, Cg g else 0 := by
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, forall_true_left]
  rw [hprod]
  by_cases ha : allowed <;> by_cases hb : ∀ g, Lg g <;> by_cases hs : smallLegal <;>
    simp [ha, hb, hs, P] <;> ring


set_option pp.fullNames true
end Green64FullPhysicalE

end

end

