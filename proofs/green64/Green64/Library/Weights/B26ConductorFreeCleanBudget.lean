module

public import Green64.Library.Weights.Part083

@[expose] public section

/-!
# Weights / B26ConductorFreeCleanBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26ConductorFreeCleanBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal full canonical two-block CLEAN packet has a conductor-free
one-visit energy budget: the actual RAW budget plus the proved arithmetic
CLEAN-minus-RAW error. All four endpoint signs and the unrestricted joint
future survive. SourceComparisonData and the true prime geometry remain
explicit inputs; this is not an N-step or complete source03 matrix claim. -/
theorem eventually_source_original_B26_NODUP_FULL_CLEAN_CONDUCTOR_FREE434
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
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (cap : G → ℕ)
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
      (epsSrc epsTgt : Bool)
      (f : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) cap → Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap
      data.Vsmall data.Vbig mu
      (sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    (2*(sourceOriginalB26RawFamilyHilbertBudget434 data.Tb J ell m hmJ
        blockA blockB q data.Vsmall mu + L^(-Bgoal)))*sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_FULL_ORDERED_CLEAN_RAW_SAVING434
      cfg gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent J,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hMain hVisit
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig cap
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm hmJ zeta theta o k ho hk0 hZeta hk epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let State := FullPhysicalState SP sm BP (fun _ => Subtype.val) (J+ell) cap
  let E := sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
    J ell cap data.Vsmall data.Vbig mu
  let C := sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
    J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f
  let R := sourceOriginalB26NodupFullOrderedRaw434 data SP sm cap q N blockA blockB
    J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f
  let Err := fun a S => C a S-R a S
  let budget := sourceOriginalB26RawFamilyHilbertBudget434 data.Tb J ell m hmJ blockA blockB q data.Vsmall mu
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) : 0 < physicalSourceBaseline BP (fun _ => Subtype.val) q N g p := by
    have hz := (source_original_B26_physical_baseline_half434 BP (fun _ => Subtype.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hz]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVb g) (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  have hi : Function.Injective (fun p : Sigma BP => p.2.val) := by
    rintro ⟨g,⟨p,hp⟩⟩ ⟨j,⟨v,hv⟩⟩ he
    dsimp only at he
    subst v
    have hg := sep.hBB g j p hp hv
    subst j
    rfl
  have hBound := hMain x Y Hprime data SP sm cap sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hDisjoint
    m hm hmJ zeta theta o k ho hk0 hZeta hk epsSrc epsTgt f
  refine ⟨hBound.1,?_⟩
  have hErr : E Err ≤ L^(-Bgoal)*E f := by
    have ht := hBound.2
    rw [source_original_B26_NODUP_FULL_CLEAN_RAW_difference434] at ht
    exact ht
  have hRaw : E R ≤ budget*E f :=
    source_original_B26_NODUP_RAW_FULL_ORDERED_Hilbert434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt hq hq1 ho hi hmu f
  let w := sourceOriginalMemoryFullDensityMass434 SP sm BP (fun _ => Subtype.val)
    J ell cap data.Vsmall data.Vbig mu
  have hw (a : State) : 0 ≤ w a :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu hVs hVb hmu a
  have hp (a : State) (S : Finset ℕ) :
      ‖C a S‖^2 ≤ 2*(‖Err a S‖^2+‖R a S‖^2) := by
    have hn := norm_add_le (C a S-R a S) (R a S)
    rw [sub_add_cancel] at hn
    change ‖C a S‖^2 ≤ 2*(‖C a S-R a S‖^2+‖R a S‖^2)
    nlinarith [norm_nonneg (C a S),norm_nonneg (C a S-R a S),norm_nonneg (R a S),
      sq_nonneg (‖C a S-R a S‖-‖R a S‖)]
  have hTri : E C ≤ 2*(E Err+E R) := by
    calc
      _ ≤ ∑ a : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP (fun _ => Subtype.val)).powerset,
          2*(w a*‖Err a S‖^2+w a*‖R a S‖^2) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro S hS
        have ht := mul_le_mul_of_nonneg_left (hp a S) (hw a)
        nlinarith only [ht]
      _ = _ := by
        simp only [E,sourceOriginalMarkedOrderedEnergy434,w,
          mul_add,Finset.sum_add_distrib,Finset.mul_sum]
        rfl
  change E C ≤ (2*(budget+L^(-Bgoal)))*E f
  calc
    _ ≤ 2*(E Err+E R) := hTri
    _ ≤ 2*(L^(-Bgoal)*E f+budget*E f) :=
      mul_le_mul_of_nonneg_left (add_le_add hErr hRaw) (by norm_num)
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

end

