module

public import Green64.Library.Weights.Part057
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.B26TiltedAuxBanBlockIdentity
public import Green64.Library.Weights.B26TiltedComparisonBlockIdentity
public import Green64.Library.Weights.B26TiltedGenuineCoherentDecomposition

@[expose] public section

/-!
# Weights / Part058

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26TiltedHomogeneousComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 44000000

/-- Physical tilted comparison at the ORIGINAL visit depth. The density loss
2*Ctilt is chosen before conductor/mesh parameters. The threshold precedes
all moving groups, J, full endpoint tests and permutations; auxiliary draws
remain harmonic. All four shared endpoint signs are retained. --/
theorem eventually_source_original_B26_TILTED_HOMOGENEOUS_COMPARISON434
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
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (J : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (ES ET : ℝ) (hES0 : 0 ≤ ES) (hET0 : 0 ≤ ET)
      (sourceTest targetTest :
        (ν : SourceOriginalProbePattern434 G m) →
        ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
      (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26TiltedFullActiveEnergy434
          data q (2*Nat.ceil (L^(0.52:ℝ))) J ell m hmJ sourceTest ν ∧
        sourceOriginalB26TiltedFullActiveEnergy434
          data q (2*Nat.ceil (L^(0.52:ℝ))) J ell m hmJ sourceTest ν ≤ ES)
      (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26TiltedFullActiveEnergy434
          data q (2*Nat.ceil (L^(0.52:ℝ))) J ell m hmJ targetTest ν ∧
        sourceOriginalB26TiltedFullActiveEnergy434
          data q (2*Nat.ceil (L^(0.52:ℝ))) J ell m hmJ targetTest ν ≤ ET)
      (epsSrc epsTgt : Bool),
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J) + ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 G m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalB26TiltedPermutedFullPairing434
        data q (2*Nat.ceil (L^(0.52:ℝ))) J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 ≤ L^(-Bgoal)*ES*ET := by
  let Ct := sourceOriginalB26TiltDensityExponent434 ell cfg.tmax cfg.C0
  have hCt : 0 ≤ Ct := source_original_B26_tilt_density_exponent_nonneg434
    ell cfg.tmax cfg.C0 cfg.hC0
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_HOMOGENEOUS_ALL_NU_COMPARISON434
      cfg gamma dscale (Bgoal+2*Ct) Cfreq Ck hgamma hd
      (by linarith only [hGoal,hCt]) hCk
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1 sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ ζ k c theta orientation hDivisor hOrientation hZeta hk
    sigma tau ES ET hES0 hET0 sourceTest targetTest hES hET epsSrc epsTgt
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val) q N g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
  have hb0 (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := hb g p
    linarith only [hh]
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast (data.hTbPrime g p.val p.property).pos
    exact div_pos (one_div_pos.mpr hp) (hVpos g)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hCap (perm : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (F : (ν : SourceOriginalProbePattern434 G m) → ((g : G) → Fin (J+ell) → BP g) → ℂ)
      (ν : SourceOriginalProbePattern434 G m) :
      0 ≤ sourceOriginalB26FullActiveEnergy434 data J ell m hmJ
        (sourceOriginalB26PhysicalTiltTest434 data q N J ell m hmJ perm F) ν ∧
      sourceOriginalB26FullActiveEnergy434 data J ell m hmJ
        (sourceOriginalB26PhysicalTiltTest434 data q N J ell m hmJ perm F) ν ≤
        L^Ct*sourceOriginalB26TiltedFullActiveEnergy434 data q N J ell m hmJ F ν := by
    constructor
    · exact source_original_B26_active_energy_nonneg434 BP J ell mu hmu _
    · exact source_original_B26_PHYSICAL_TILT_ENDPOINT_CAP434 BP (fun _ p => p.val)
        q N data.Vbig hVpos hb J ell m cfg.tmax hmJ hm ν (perm ν) (F ν)
        cfg.C0 L hL data.hBigGroups
  let u := sourceOriginalB26PhysicalTiltTest434 data q N J ell m hmJ sigma sourceTest
  let v := sourceOriginalB26PhysicalTiltTest434 data q N J ell m hmJ tau targetTest
  have hu : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalB26FullActiveEnergy434 data J ell m hmJ u ν ∧
      sourceOriginalB26FullActiveEnergy434 data J ell m hmJ u ν ≤ L^Ct*ES := by
    intro ν hν
    exact ⟨(hCap sigma sourceTest ν).1,(hCap sigma sourceTest ν).2.trans
      (mul_le_mul_of_nonneg_left (hES ν hν).2 (Real.rpow_nonneg hLp.le _))⟩
  have hv : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalB26FullActiveEnergy434 data J ell m hmJ v ν ∧
      sourceOriginalB26FullActiveEnergy434 data J ell m hmJ v ν ≤ L^Ct*ET := by
    intro ν hν
    exact ⟨(hCap tau targetTest ν).1,(hCap tau targetTest ν).2.trans
      (mul_le_mul_of_nonneg_left (hET ν hν).2 (Real.rpow_nonneg hLp.le _))⟩
  obtain ⟨hModes,hBound⟩ := hMain x Y Hprime data sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J ell hmJ ζ k c theta orientation
    hDivisor hOrientation hZeta hk sigma tau (L^Ct*ES) (L^Ct*ET)
    (mul_nonneg (Real.rpow_nonneg hLp.le _) hES0)
    (mul_nonneg (Real.rpow_nonneg hLp.le _) hET0) u v hu hv epsSrc epsTgt
  refine ⟨hModes,?_⟩
  have hEq (ν : SourceOriginalProbePattern434 G m) :=
    sourceOriginalB26TiltedPermutedFullPairing434_eq_harmonic434
      data q N J ell m hmJ (Nat.ceil (4*L^(D+Ck+1)))
      (fun _ => Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (fun _ => Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (L^(-(Cxi:ℝ))) ζ c theta orientation k sigma tau sourceTest targetTest ν hb0
  dsimp only [N] at hEq
  simp_rw [hEq]
  have hBudget : L^(-(Bgoal+2*Ct))*(L^Ct)^2 = L^(-Bgoal) := by
    rw [← Real.rpow_two,← Real.rpow_mul hLp.le,← Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ L^(-(Bgoal+2*Ct))*(L^Ct*ES)*(L^Ct*ET) := hBound
    _ = (L^(-(Bgoal+2*Ct))*(L^Ct)^2)*(ES*ET) := by ring
    _ = L^(-Bgoal)*ES*ET := by rw [hBudget];ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26TiltedSmallOldAuxBanIdentity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Exact comparison component at the ORIGINAL CLEAN SMALL/Fourier
call site, with the same sector mass and both physical P_d maps. -/
theorem source_original_B26_TILTED_CANONICAL_SMALL_OLD_AUX_BAN_IDENTITY434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) :
    sourceOriginalB26TiltedCanonicalSmallOldAuxBanPair434 data N SP smallMod
      blockA blockB J ell m hmJ sizes prime Q h xi q ζ theta o k epsSrc epsTgt U F =
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let bigMod := fun (g : G) (p : BP g) => p.val
    let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
    let Torus := memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
    let PU := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := U)
    let PF := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := F)
    (Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell):ℂ) *
      (Fintype.card Torus:ℂ) *
      ∑ ss : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ d : SourceOriginalB26SharedTuple434 SP J ell,
      ∑ a : SourceOriginalB26Active434 BP J ell,
      ∑ psi : AddChar Torus ℂ,
        (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime data.Vsmall mu a:ℂ) *
        (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr (PU ss d a) psi) *
        sourceOriginalB26TiltedCanonicalAuxBanBlock434 data q N blockA blockB
          J ell m hmJ Q h xi ζ
          (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
          o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
          (fun b => (AddChar.complexBasis Torus).repr (PF tt d b) psi) a := by
  classical
  unfold sourceOriginalB26TiltedCanonicalSmallOldAuxBanPair434 sourceOriginalB26SmallOldLiftedPair434
  dsimp only
  simp_rw [source_original_B26_TILTED_CANONICAL_AUX_BAN_FORM_BLOCK434,
    source_original_B26_sector_mass_factor434]
  simp only [Finset.mul_sum,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.star_def]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro psi _
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26TiltedSmallOldPairIdentity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Exact comparison component at the ORIGINAL CLEAN SMALL/Fourier
call site, with the same sector mass and both physical P_d maps. -/
theorem source_original_B26_TILTED_CANONICAL_SMALL_OLD_COMPARISON_IDENTITY434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) :
    sourceOriginalB26TiltedCanonicalSmallOldComparisonPair434 data N SP smallMod
      blockA blockB J ell m hmJ sizes prime Q h xi q ζ theta o k epsSrc epsTgt U F =
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let bigMod := fun (g : G) (p : BP g) => p.val
    let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
    let Torus := memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
    let PU := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := U)
    let PF := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := F)
    (Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell):ℂ) *
      (Fintype.card Torus:ℂ) *
      ∑ ss : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ d : SourceOriginalB26SharedTuple434 SP J ell,
      ∑ a : SourceOriginalB26Active434 BP J ell,
      ∑ psi : AddChar Torus ℂ,
        (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime data.Vsmall mu a:ℂ) *
        (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr (PU ss d a) psi) *
        sourceOriginalB26TiltedCanonicalComparisonBlock434 data q N blockA blockB
          J ell m hmJ Q h xi ζ
          (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
          o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
          (fun b => (AddChar.complexBasis Torus).repr (PF tt d b) psi) a := by
  classical
  unfold sourceOriginalB26TiltedCanonicalSmallOldComparisonPair434 sourceOriginalB26SmallOldLiftedPair434
  dsimp only
  simp_rw [source_original_B26_TILTED_CANONICAL_COMPARISON_FORM_BLOCK434,
    source_original_B26_sector_mass_factor434]
  simp only [Finset.mul_sum,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.star_def]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro psi _
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26TiltedCanonicalSmallOldRaw -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Actual RAW Fourier term in the same physical SMALL/OLD sector. -/
def sourceOriginalB26TiltedCanonicalSmallOldRawPair434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) : ℂ :=
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let bigMod := fun (g : G) (p : BP g) => p.val
    let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
    let Torus := memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
    let PU := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := U)
    let PF := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
      J ell sizes prime q data.Vsmall (U := F)
    (Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell):ℂ) *
      (Fintype.card Torus:ℂ) *
      ∑ ss : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell),
      ∑ d : SourceOriginalB26SharedTuple434 SP J ell,
      ∑ a : SourceOriginalB26Active434 BP J ell,
      ∑ psi : AddChar Torus ℂ,
        (sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime data.Vsmall mu a:ℂ) *
        (starRingEnd ℂ) ((AddChar.complexBasis Torus).repr (PU ss d a) psi) *
        sourceOriginalB26TiltedCanonicalRawBlock434 data q N blockA blockB
          J ell m hmJ Q h xi ζ
          (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
          o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)
          (fun b => (AddChar.complexBasis Torus).repr (PF tt d b) psi) a

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26TiltedPhysicalCleanRawDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Literal CLEAN minus its RAW Fourier term is exactly the comparison
minus the genuine auxiliary-ban correction, in a fixed physical OLD sector.
The genuine probe family is enumerated once; no norm is used here. -/
theorem source_original_B26_TILTED_SECTOR_CLEAN_RAW_RESIDUAL434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ)
    (hBlocks : Disjoint blockA blockB) (hq : 0 ≤ q)
    (hVs : ∀ g,0 < data.Vsmall g) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let bigMod := fun (g : G) (p : BP g) => p.val
    let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    sourceOriginalB26SectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime
      (fun n : ↥family => sourceOriginalProbeMemoryPattern434 J m hmJ n.val)
      mu data.Vbig
      (fun n : ↥family => sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig
        J ell m hmJ n.val Q h h xi)
      q data.Vsmall ζ theta o k U F =
    sourceOriginalB26TiltedCanonicalSmallOldRawPair434 data N SP smallMod blockA blockB
      J ell m hmJ cap sizes hsizes prime Q h xi q ζ theta o k false false U F +
    sourceOriginalB26TiltedCanonicalSmallOldComparisonPair434 data N SP smallMod blockA blockB
      J ell m hmJ sizes prime Q h xi q ζ theta o k false false U F -
    sourceOriginalB26TiltedCanonicalSmallOldAuxBanPair434 data N SP smallMod blockA blockB
      J ell m hmJ sizes prime Q h xi q ζ theta o k false false U F := by
  classical
  dsimp only
  rw [source_original_B26_CLEAN_SMALL_PHYSICAL_FOURIER_PAIR434
    SP smallMod _ (fun _ p => p.val) J ell m cap sizes hsizes prime
    _ _ _ _ q hq data.Vsmall hVs ζ theta o k U F]
  rw [source_original_B26_TILTED_CANONICAL_SMALL_OLD_COMPARISON_IDENTITY434
    data N SP smallMod blockA blockB J ell m hmJ cap sizes hsizes prime
    Q h xi q ζ theta o k false false U F,
    source_original_B26_TILTED_CANONICAL_SMALL_OLD_AUX_BAN_IDENTITY434
    data N SP smallMod blockA blockB J ell m hmJ cap sizes hsizes prime
    Q h xi q ζ theta o k false false U F]
  unfold sourceOriginalB26TiltedCanonicalSmallOldRawPair434
  dsimp only
  simp_rw [source_original_B26_TILTED_GENUINE_COHERENT_RAW_COMPARISON_BAN434
    data q N blockA blockB hBlocks J ell m hmJ Q h xi ζ _ o k ho hk]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]

/-- Exact same decomposition for arbitrary tests on the ORIGINAL physical
state and symmetric Fock output, via their actual source/target pullbacks. -/
theorem source_original_B26_TILTED_ORIGINAL_CLEAN_RAW_RESIDUAL434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ)
    (U : FullPhysicalState SP smallMod (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) (J+ell) cap → ℂ)
    (F : FullPhysicalOutput SP smallMod (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) (J+ell) → ℂ)
    (hBlocks : Disjoint blockA blockB) (hq : 0 ≤ q)
    (hVs : ∀ g,0 < data.Vsmall g) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let bigMod := fun (g : G) (p : BP g) => p.val
    let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let U' := sourceOriginalB26SourcePullback434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime U
    let F' := sourceOriginalB26TargetPullback434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime F
    sourceOriginalB26LiteralSectorCleanPair434 SP smallMod BP bigMod J ell m cap
      sizes hsizes prime
      (fun n : ↥family => sourceOriginalProbeMemoryPattern434 J m hmJ n.val)
      mu data.Vbig
      (fun n : ↥family => sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig
        J ell m hmJ n.val Q h h xi)
      q data.Vsmall ζ theta o k U F =
    sourceOriginalB26TiltedCanonicalSmallOldRawPair434 data N SP smallMod blockA blockB
      J ell m hmJ cap sizes hsizes prime Q h xi q ζ theta o k false false U' F' +
    sourceOriginalB26TiltedCanonicalSmallOldComparisonPair434 data N SP smallMod blockA blockB
      J ell m hmJ sizes prime Q h xi q ζ theta o k false false U' F' -
    sourceOriginalB26TiltedCanonicalSmallOldAuxBanPair434 data N SP smallMod blockA blockB
      J ell m hmJ sizes prime Q h xi q ζ theta o k false false U' F' := by
  classical
  dsimp only
  rw [source_original_B26_CLEAN_LITERAL_SECTOR_PAIR434]
  exact source_original_B26_TILTED_SECTOR_CLEAN_RAW_RESIDUAL434 data N SP smallMod blockA blockB
    J ell m hmJ cap sizes hsizes prime Q h xi q ζ theta o k _ _ hBlocks hq hVs ho hk
end Green64Analytic.CorrelationSquare

end

end

