module

public import Green64.Library.Weights.Part076
public import Green64.Library.Weights.Part062
public import Green64.Library.Weights.Part026
public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Weights / Part077

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26MarkedResidueHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Perm" => BigGroupPerm (BG := G) (J+ell)
local notation "pat" => sourceOriginalProbeMemoryPattern434 J m hmJ nu

/-- On each nonzero literal shared-copy summand, the original FULL divisor
can be read at either endpoint, with its own independent permutation. -/
theorem source_original_B26_CLEAN_nonzero_divisor_transport434
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat)
    (mu : (g : G) → BP g → ℝ) (sigma tau : Perm) (s t : A)
    (h : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau ≠ 0) :
    sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux s sigma =
    sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux t tau := by
  have hc (g : G) (i : Fin (J+ell)) (hi : i ∈ sourceBigShared J ell m pat g) :
      t g (tau g i) = s g (sigma g i) := by
    unfold sourceOriginalB26FrozenFreshLaw434 at h
    have hg := Finset.prod_ne_zero_iff.mp h g (Finset.mem_univ g)
    have ht := Finset.prod_ne_zero_iff.mp hg (tau g i) (Finset.mem_univ _)
    simp only [Equiv.symm_apply_apply,if_pos hi] at ht
    by_contra hn
    exact ht (if_neg hn)
  unfold sourceOriginalB26FrozenD434
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (bm g) (hc g i hi).symm

variable {R : Type} [Fintype R] [AddCommGroup R]

/-- Counting all original frozen residue coordinates, with the SAME
active density and numerical-history carrier as the marked CLEAN bound. -/
def sourceOriginalB26NumericResidueEnergy434
    (mu : (g : G) → BP g → ℝ) (f : A → Finset ℕ → R → ℂ) : ℝ :=
  ∑ r : R,sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
    (fun s S => f s S r)

/-- Arbitrary target-dependent residue translations preserve this energy
exactly; no number of residues or Fourier modes is charged. -/
theorem source_original_B26_MARKED_RESIDUE_energy_shift434
    (mu : (g : G) → BP g → ℝ) (c : A → Finset ℕ → R)
    (f : A → Finset ℕ → R → ℂ) :
    sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu
      (fun s S r => f s S (r+c s S)) =
    sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu f := by
  unfold sourceOriginalB26NumericResidueEnergy434 sourceOriginalB26NumericActiveEnergy434
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  change (∑ r : R,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    ∑ s : A,w s*‖f s S (r+c s S)‖^2) = _
  have hs (s : A) (S : Finset ℕ) :
      (∑ r : R,w s*‖f s S (r+c s S)‖^2) = ∑ r : R,w s*‖f s S r‖^2 := by
    exact Fintype.sum_equiv (Equiv.addRight (c s S)) _ _ (fun _ => rfl)
  calc
    _ = ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ s : A,∑ r : R,w s*‖f s S (r+c s S)‖^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ s : A,∑ r : R,w s*‖f s S r‖^2 := by simp_rw [hs]
    _ = _ := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm

/-- The literal source-D residue translation remains INSIDE each marked
CLEAN summand, on the same updated numerical seen. K may depend on the
current full residue vector, in particular through OLD endpoint masks. -/
def sourceOriginalB26NumericResidueClean434
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat) (o k : ℤ) (shift : ℤ → R)
    (mu : (g : G) → BP g → ℝ) (sigma tau : Perm)
    (K : R → A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → R → ℂ)
    (s : A) (S : Finset ℕ) (r : R) : ℂ :=
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S then
    ∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT t)).image
          (fun p : Sigma BP => bm p.1 p.2)) then
        K r (eS s) S (eT t) *
          f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT t)).image
            (fun p : Sigma BP => bm p.1 p.2))
            (r+shift (o*k*(sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux s sigma:ℤ)))
       else 0)
  else 0

/-- Exact transport to a target-dependent translation. It is the original
nonzero shared-copy law, not an independence of D and the joint future. -/
theorem source_original_B26_MARKED_RESIDUE_target_transport434
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat) (o k : ℤ) (shift : ℤ → R)
    (mu : (g : G) → BP g → ℝ) (sigma tau : Perm)
    (K : R → A → Finset ℕ → A → ℂ) (f : A → Finset ℕ → R → ℂ)
    (s : A) (S : Finset ℕ) (r : R) :
    sourceOriginalB26NumericResidueClean434 BP bm J ell m hmJ nu
      dsmall aux o k shift mu sigma tau K f s S r =
    sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu sigma tau (K r)
      (fun t T => f t T
        (r+shift (o*k*(sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux t tau:ℤ))))
      s S := by
  unfold sourceOriginalB26NumericResidueClean434 sourceOriginalB26NumericPermutedClean434
  dsimp only
  split_ifs with hs
  · apply Finset.sum_congr rfl
    intro t ht
    by_cases hz : sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau=0
    · simp only [hz,zero_mul]
    · rw [source_original_B26_CLEAN_nonzero_divisor_transport434 BP bm J ell m hmJ nu
        dsmall aux mu sigma tau s t hz]
  · rfl

/-- Full marked active×numeric-seen×frozen-residue Hilbert gain for one
actual CLEAN pattern/auxiliary term and both endpoint permutations.
All original pending/SMALL residue coordinates can be used as R; arbitrary
complex futures and residue-dependent caps are allowed. The density and
residue counting remain unchanged. -/
theorem source_original_B26_MARKED_RESIDUE_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat) (o k : ℤ) (shift : ℤ → R)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p) (sigma tau : Perm)
    (C : ℝ) (hC : 0 ≤ C)
    (K : R → A → Finset ℕ → A → ℂ) (hK : ∀ r s S t,‖K r s S t‖ ≤ C)
    (f : A → Finset ℕ → R → ℂ) :
    sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericResidueClean434 BP bm J ell m hmJ nu
        dsmall aux o k shift mu sigma tau K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu f := by
  let delta := C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)
  let c (t : A) (_ : Finset ℕ) :=
    shift (o*k*(sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux t tau:ℤ))
  calc
    _ = ∑ r : R,sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
        (sourceOriginalB26NumericPermutedClean434 BP bm J ell m hmJ nu mu sigma tau (K r)
          (fun t T => f t T (r+c t T))) := by
      unfold sourceOriginalB26NumericResidueEnergy434
      simp_rw [source_original_B26_MARKED_RESIDUE_target_transport434]
      rfl
    _ ≤ ∑ r : R,delta*sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
        (fun t T => f t T (r+c t T)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact source_original_B26_NUMERIC_permuted_Hilbert434 BP bm J ell m hmJ nu
        hi mu hmu sigma tau C hC (K r) (hK r) _
    _ = delta*sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu f := by
      rw [← Finset.mul_sum]
      congr 1
      exact source_original_B26_MARKED_RESIDUE_energy_shift434 BP bm J ell mu c f

/-- Instantiate the translation with the ORIGINAL full frozen residue
group: every SMALL coordinate and every ordered Fock/OLD occurrence uses
its actual modulus and the signed original step o*k*D. -/
theorem source_original_B26_MARKED_ORIGINAL_TORUS_Hilbert434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → BP g)
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat) (o k : ℤ)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p) (sigma tau : Perm)
    (C : ℝ) (hC : 0 ≤ C)
    (K : memoryFrozenResidueGroup SP sm BP bm sizes prime → A → Finset ℕ → A → ℂ)
    (hK : ∀ r s S t,‖K r s S t‖ ≤ C)
    (f : A → Finset ℕ → memoryFrozenResidueGroup SP sm BP bm sizes prime → ℂ) :
    sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericResidueClean434 BP bm J ell m hmJ nu
        dsmall aux o k (memoryFrozenResidueShift SP sm BP bm sizes prime)
        mu sigma tau K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu f := by
  exact source_original_B26_MARKED_RESIDUE_Hilbert434 BP bm J ell m hmJ nu hi
    dsmall aux o k (memoryFrozenResidueShift SP sm BP bm sizes prime)
    mu hmu sigma tau C hC K hK f

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalNumericResidueAuxBan -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Actual auxiliary/ACTIVE ban saving on physical active times seen
times the complete SMALL/OLD residue group, with its literal divisor
translations. No residue, character, or history count is incurred. -/
theorem eventually_source_original_B26_PHYSICAL_NUMERIC_RESIDUE_AUX_BAN434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (J m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (ho : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu f := by
  filter_upwards [eventually_source_original_B26_PHYSICAL_NUMERIC_ALL_NU_AUX_BAN434
    cfg ell Cslots Bgoal Cq Cxi] with L hMain
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime q hq hq1
    hVbig hTbLower blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi
    hhA hhB hxi hQ hXi zeta k c theta orientation ho sigma tau epsSrc epsTgt f
  classical
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  rw [source_original_B26_NUMERIC_RESIDUE_AUX_BAN_FOURIER434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
    sigma tau epsSrc epsTgt f]
  apply source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val))
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) (L^(-Bgoal))
  intro psi g
  exact hMain x Y Hprime data q hq hq1 hVbig hTbLower
    blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi hhA hhB hxi hQ hXi
    zeta k c (fun nu => theta nu+sourceOriginalB26ModeAngle434
      SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
    orientation ho sigma tau epsSrc epsTgt g

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalNumericResidueComparison -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Arithmetic saving for the LITERAL unbanned auxiliary-minus-RAW
evolution on physical tilted active primes times numerical seen times
the complete original frozen SMALL/OLD residue group. Every auxiliary
and RAW divisor is translated separately before Fourier expansion.
Both endpoint permutations, coherent probe signs and arbitrary coupled
complex futures remain present. There is no residue/frequency/history
count loss. The source threshold precedes every moving OLD sector.

SMALL half-map synthesis, the auxiliary ban and global RAW-chain control
are separate from this theorem. The SourceComparisonData fields remain
explicit; no constructor or original global correlation is asserted. -/
theorem eventually_source_original_B26_PHYSICAL_NUMERIC_RESIDUE_COMPARISON_ERROR434
    (cfg : SourceComparisonFixed434) (ell : ℕ)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g,data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g,loB g ≤ hiB g)
      (hBigUpper : ∀ g,(hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g,Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (J : ℕ) (hmJ : m ≤ J)
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<c nu)
      (hOrientation : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_PHYSICAL_NUMERIC_ALL_NU_COMPARISON_ERROR434
      cfg ell gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent] with L hMain
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime q hq hq1
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ zeta k c theta orientation
    hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  have hLocal (angle : SourceOriginalProbePattern434 G m → ℝ)
      (g : A → Finset ℕ → ℂ) :=
    hMain x Y Hprime data q hq hq1 sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ zeta k c angle orientation
      hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt g
  refine ⟨(hLocal theta (fun _ _ => 0)).1,?_⟩
  rw [source_original_B26_NUMERIC_RESIDUE_COMPARISON_FOURIER434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta c theta orientation k
    sigma tau epsSrc epsTgt hDisjoint f]
  apply source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val))
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) (L^(-Bgoal))
  intro psi g
  exact (hLocal (fun nu => theta nu+sourceOriginalB26ModeAngle434
    SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)) g).2

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMarkedSmallEndpoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (J ell : ℕ)
local notation "Small" => GroupState SP sm (J+ell)
local notation "ST" => GroupTorus SP sm
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Perm" => GroupPermFamily (G := SG) (J+ell)

/-- The actual adjoint endpoint map: the source's own shared labels and
full residue are read once. No independent conditional state is sampled. -/
def sourceOriginalSmallEndpointSynthesis434
    (q : ℝ) (Vs : SG → ℝ) (ss : Perm) (F : Shared → ST → ℂ) (xs : Small) : ℂ :=
  (memoryOriginalSmallGroupPhysicalEndpointHalf SP sm J ell q Vs
    (memoryOriginalSmallGroupResidue SP sm (J+ell) xs) : ℂ) *
  F (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs)
    (memoryOriginalSmallGroupResidue SP sm (J+ell) xs)

/-- The true SMALL synthesis map has the SAME fixed conditioning cost as
the already proved half-map, independent of J and of the residue moduli. -/
theorem source_original_SMALL_endpoint_synthesis_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (ss : Perm) (F : Shared → ST → ℂ) :
    (∑ xs : Small,‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      (∑ d : Shared,∑ y : ST,‖F d y‖^2) := by
  let label := memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss
  let res := memoryOriginalSmallGroupResidue SP sm (J+ell)
  let a := memorySmallGroupConditionalRatio SP sm J ell q Vs
  let cost := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  let T := memoryFiniteConditionalFibre label res
  have hpoint (d : Shared) (y : ST) (xs : Small) (hx : xs ∈ T d y) :
      ‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2 =
      a y*‖F d y‖^2 := by
    have hx' : label xs=d ∧ res xs=y := by
      simpa only [T,memoryFiniteConditionalFibre,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    change ‖(memoryOriginalSmallGroupPhysicalEndpointHalf SP sm J ell q Vs (res xs):ℂ) *
      F (label xs) (res xs)‖^2 = _
    rw [hx'.1,hx'.2,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      memory_original_small_group_endpoint_half_sq SP sm J ell q hq.le Vs hVs]
  rw [←memory_finite_conditional_partition label res
    (fun xs => ‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2)]
  calc
    _ = ∑ d : Shared,∑ y : ST,(a y*((T d y).card:ℝ))*‖F d y‖^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = ∑ xs ∈ T d y,a y*‖F d y‖^2 :=
          Finset.sum_congr rfl (fun xs hx => hpoint d y xs hx)
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ d : Shared,∑ y : ST,cost*‖F d y‖^2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact source_original_small_group_permuted_fibre_weight434 SP sm J ell q hq hq1
        Vs hVs (sourceSmallShared J ell) (source_original_B26_small_shared_card434 J ell)
        ss d y
    _ = _ := by simp only [cost,Finset.mul_sum]

/-- Exact original SMALL row = source synthesis times target half-map.
The step is the real signed integer displacement, and the two endpoint
permutations remain independent. This is an identity of actual kernels. -/
theorem source_original_SMALL_row_endpoint_factor434
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (step : ℤ) (ss tt : Perm) (xs : Small) (f : Small → ℂ) :
    (∑ ys : Small,groupPermutedKernel SP sm (J+ell) q Vs
      (sourceSmallShared J ell) step (fun _ _ => 1) ss tt xs ys * f ys) =
    (memoryOriginalSmallGroupPhysicalEndpointHalf SP sm J ell q Vs
      (memoryOriginalSmallGroupResidue SP sm (J+ell) xs) : ℂ) *
      memoryOriginalSmallPermutedHalfMap SP sm J ell q Vs (sourceSmallShared J ell)
        tt (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs)
        (groupTranslate SP sm step (memoryOriginalSmallGroupResidue SP sm (J+ell) xs)) f := by
  simp only [memoryOriginalSmallPermutedHalfMap,memoryOriginalSmallGroupPermutedFibre,
    memoryFiniteConditionalFibre,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_congr rfl
  intro ys hys
  rw [memory_original_group_small_physical_kernel_half SP sm J ell q hq Vs hVs
    (sourceSmallShared J ell) (source_original_B26_small_shared_card434 J ell)]
  have he := memory_original_small_group_edge_conditional_iff SP sm (J+ell)
    (sourceSmallShared J ell) step ss tt xs ys
  by_cases h : groupEdgeAllowedPerm SP sm (J+ell) (sourceSmallShared J ell) step ss tt xs ys
  · obtain ⟨hd,hy⟩ := he.mp h
    rw [if_pos h,if_pos ⟨hd.symm,hy⟩]
    rw [hy]
    ring
  · have hn : ¬(memoryOriginalSmallGroupSharedLabels SP sm (J+ell)
        (sourceSmallShared J ell) tt ys =
          memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs ∧
        memoryOriginalSmallGroupResidue SP sm (J+ell) ys =
          groupTranslate SP sm step (memoryOriginalSmallGroupResidue SP sm (J+ell) xs)) :=
      fun hxy => h (he.mpr ⟨hxy.1.symm,hxy.2⟩)
    simp only [if_neg h,if_neg hn,zero_mul]

end Green64Analytic.CorrelationSquare

end

end

