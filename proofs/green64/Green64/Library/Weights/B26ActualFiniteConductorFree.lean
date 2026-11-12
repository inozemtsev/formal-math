module

public import Green64.Library.Correlation.B26CanonicalPhysicalBridge
public import Green64.Library.Weights.B26SharpCleanBudget
public import Green64.Library.Weights.Part083

@[expose] public section

/-!
# Weights / B26ActualFiniteConductorFree

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26ActualFiniteConductorFree -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

section Transfer
variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
variable (data : SourceComparisonData434 SG G cfg x L Y Hp)
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (cap : G → ℕ) (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
local notation "BP" => (fun g => {p : ℕ // p ∈ data.Tb g})
local notation "State" => FullPhysicalState SP sm BP (fun _ => Subtype.val) (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP (fun _ => Subtype.val) (J+ell)
local notation "Hist" => sourceOriginalActualSignedHistoryState434 SP sm BP (fun _ => Subtype.val) J ell cap
local notation "mu" => physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
local notation "family" => sourceOriginalTwoBlockProbePatterns434 blockA blockB m
local notation "nu" => (fun v : family => Subtype.val v)
local notation "patterns" => (fun v : family => sourceOriginalProbeMemoryPattern434 J m hmJ (Subtype.val v))
local notation "K" => (fun v : family =>
  sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig J ell m hmJ (Subtype.val v) Q h h xi)

private theorem finite_masked_from_ordered
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hmu : ∀ g p,0 < mu g p)
    (budget : ℝ) (hbudget : 0 ≤ budget)
    (hOrdered : ∀ f : State → Finset ℕ → ℂ,
      sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap
        data.Vsmall data.Vbig mu
        (sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
          J ell m hmJ Q h xi zeta theta o k false false f) ≤
      budget * sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
        J ell cap data.Vsmall data.Vbig mu f)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (T : ℕ) (f : Hist → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
        J ell cap data.Vsmall data.Vbig mu)
      (fun a : Hist => ∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP (fun _ => Subtype.val) J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
        q rho data.Vsmall data.Vbig mu K zeta theta o k T a b * f b) ≤
    budget * sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
        J ell cap data.Vsmall data.Vbig mu) f := by
  have hVs (g : SG) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
    J ell cap data.Vsmall data.Vbig mu
  let E := sourceOriginalSignedJointForwardEnergy434 pi
  have hOrbit (F : Out → Finset ℕ → ℂ) :
      sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap
        data.Vsmall data.Vbig mu
        (sourceOriginalMarkedCleanOrbitFamily434 SP sm BP (fun _ => Subtype.val)
          J ell m hmJ cap nu mu data.Vbig K q data.Vsmall zeta theta o k F) ≤
      budget * sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val)
        J ell cap data.Vsmall data.Vbig mu F := by
    apply le_trans (source_original_MARKED_orbit_compression_energy434 SP sm BP
      (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu _)
    have ho := hOrdered
      (fun y S => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap y) S)
    have he : sourceOriginalMarkedCleanOrderedFamily434 SP sm BP (fun _ => Subtype.val)
        J ell m hmJ cap nu mu data.Vbig K q data.Vsmall zeta theta o k
        (fun y S => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap y) S) =
      sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k false false
        (fun y S => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap y) S) := by
      funext a S
      exact (source_original_B26_CANONICAL_ordered_original434 data SP sm cap q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k _ a S).symm
    rw [he]
    rw [source_original_MARKED_ordered_orbit_energy434] at ho
    exact ho
  have hOne (g : Hist → ℂ) :
      E (sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val)
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
        q 1 data.Vsmall data.Vbig mu K zeta theta o k g) ≤ budget * E g := by
    let F := sourceOriginalActualSignedHistoryLift434 SP sm BP (fun _ => Subtype.val) J ell cap g
    let R := sourceOriginalMarkedCleanOrbitFamily434 SP sm BP (fun _ => Subtype.val)
      J ell m hmJ cap nu mu data.Vbig K q data.Vsmall zeta theta o k F
    calc
      _ = E (fun a : Hist => R a.val.1 a.val.2) := by
        congr 1
        funext a
        exact source_original_ACTUAL_CLEAN_finite_orbit_exact434 SP sm BP (fun _ => Subtype.val)
          J ell m hmJ cap nu hcap mu hmu data.Vbig K q data.Vsmall hVs zeta theta o k g a
      _ ≤ sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val)
          J ell cap data.Vsmall data.Vbig mu R :=
        source_original_ACTUAL_signed_DIRTY_reachable_le_joint_energy434 SP sm BP
          (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu R
      _ ≤ budget * sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val)
          J ell cap data.Vsmall data.Vbig mu F := hOrbit F
      _ = _ := by
        rw [source_original_ACTUAL_signed_DIRTY_lift_joint_energy_exact434
          SP sm BP (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu g]
  have hRho (g : Hist → ℂ) :
      E (sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val)
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
        q rho data.Vsmall data.Vbig mu K zeta theta o k g) ≤ budget * E g := by
    let gR : Hist → ℂ := fun b =>
      sourceOriginalMemoryOldOutput434 SP sm BP (fun _ => Subtype.val) J ell rho b.val.1 * g b
    let u : Hist → ℂ := fun a => sourceOriginalMemoryOldInput434 SP sm BP (fun _ => Subtype.val)
      J ell cap rho (sourceOriginalCanonicalPhysical434 SP sm BP (fun _ => Subtype.val) (J+ell) cap a.val.1)
    let R := sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
      q 1 data.Vsmall data.Vbig mu K zeta theta o k gR
    calc
      _ = E (fun a => u a * R a) := by
        congr 1
        funext a
        exact source_original_ACTUAL_finite_E_OLD_sandwich434 SP sm BP (fun _ => Subtype.val)
          J ell m cap patterns hcap
          (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
          q rho data.Vsmall data.Vbig mu K zeta theta o k g a
      _ ≤ E R := source_original_ACTUAL_energy_multiplier434 pi u R
        (fun a => source_original_memory_OLD_input_norm_le_one434 SP sm BP (fun _ => Subtype.val)
          J ell cap rho hrho hrho1 _)
      _ ≤ budget * E gR := hOne gR
      _ ≤ budget * E g := mul_le_mul_of_nonneg_left
        (source_original_ACTUAL_energy_multiplier434 pi
          (fun b => sourceOriginalMemoryOldOutput434 SP sm BP (fun _ => Subtype.val) J ell rho b.val.1) g
          (fun b => source_original_memory_OLD_output_norm_le_one434 SP sm BP (fun _ => Subtype.val)
            J ell rho hrho hrho1 _)) hbudget
  let gate := sourceOriginalActualSignedOLDGate434 SP sm BP (fun _ => Subtype.val) J ell cap T
  let fT : Hist → ℂ := fun b => if gate b then f b else 0
  let R := sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
    q rho data.Vsmall data.Vbig mu K zeta theta o k fT
  calc
    _ = E (fun a => if gate a then R a else 0) := by
      congr 1
      funext a
      exact (source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434 SP sm BP
        (fun _ => Subtype.val) J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
        q rho data.Vsmall data.Vbig mu K zeta theta o k T f a).symm
    _ ≤ E R := source_original_ACTUAL_energy_projector434 pi gate R
    _ ≤ budget * E fT := hRho fT
    _ ≤ budget * E f := mul_le_mul_of_nonneg_left
      (source_original_ACTUAL_energy_projector434 pi gate f) hbudget

end Transfer

/-- Unconditional conductor-free bound for the ORIGINAL finite CLEAN
comparison E matrix, with both actual OLD projectors, the true Fock×seen
density, numerical no-rebirth and arbitrary joint complex continuation.
The comparison family here has its canonical endpoint roles; it excludes
the separate RAW-none summand. J is fixed before the limit in L. -/
theorem eventually_source_original_B26_ACTUAL_COMPARISON_CLEAN_Hilbert434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck)
    (ell : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ J : ℕ, ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (cap : G → ℕ) (hcap : ∀ g,Fintype.card {p : ℕ // p ∈ data.Tb g} ≤ cap g)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g,data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g,loB g ≤ hiB g)
      (hBigUpper : ∀ g,(hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g,Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k≠0)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (T : ℕ)
      (f : sourceOriginalActualSignedHistoryState434 SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) J ell cap → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let patterns := fun v : family => sourceOriginalProbeMemoryPattern434 J m hmJ v.val
    let K := fun v : family => sourceOriginalProbeMemoryCanonicalK434
      data.Tb data.Vbig J ell m hmJ v.val Q h h xi
    let Hist := sourceOriginalActualSignedHistoryState434 SP sm BP (fun _ => Subtype.val) J ell cap
    let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalSignedJointForwardEnergy434 pi
      (fun a : Hist => ∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP (fun _ => Subtype.val) J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patterns)
        q rho data.Vsmall data.Vbig mu K zeta theta o k T a b * f b) ≤
    ((1+L^(-Bgoal))*(sourceOriginalB26SharpRawFamilyHilbertBudget434 data.Tb J ell m hmJ
      blockA blockB q data.Vsmall mu + L^(-Bgoal))) *
      sourceOriginalSignedJointForwardEnergy434 pi f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_FULL_CLEAN_SHARP_YOUNG434 cfg gamma dscale Bgoal Cfreq Ck
      hgamma hd hGoal hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent J,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
      eventually_gt_atTop (0:ℝ)] with L hMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig cap hcap sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hDisjoint
    m hm hmJ zeta theta o k ho hk0 hZeta hk rho hrho hrho1 T f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let budget := (1+L^(-Bgoal))*(sourceOriginalB26SharpRawFamilyHilbertBudget434
    data.Tb J ell m hmJ blockA blockB q data.Vsmall mu + L^(-Bgoal))
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) : 0 < physicalSourceBaseline BP (fun _ => Subtype.val) q N g p := by
    have hz := (source_original_B26_physical_baseline_half434 BP (fun _ => Subtype.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hz]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVb g) (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  have hbudget : 0 ≤ budget := by
    dsimp only [budget,sourceOriginalB26SharpRawFamilyHilbertBudget434]
    positivity
  have ha := hMain x Y Hprime data SP sm cap sep loB hiB hBigFull hLoLeHi hBigUpper
    hLoLarge hTbLower hVbig blockA blockB hDisjoint m hm hmJ zeta theta o k ho hk0 hZeta hk
    false false
  refine ⟨(ha (fun _ _ => 0)).1,?_⟩
  exact finite_masked_from_ordered data SP sm cap q N blockA blockB J ell m hmJ Q h xi
    zeta theta o k hcap hmu budget hbudget (fun F => (ha F).2) rho hrho hrho1 T f

end Green64Analytic.CorrelationSquare

end

end

