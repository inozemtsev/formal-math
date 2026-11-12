module

public import Green64.Library.Weights.B26NodupMarkedSmallMean

@[expose] public section

/-!
# Weights / B26NodupMarkedSmallCleanRawSaving

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26NodupMarkedSmallCleanRawSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem difference_history_energy
    {X Z : Type} [Fintype X] [Fintype Z]
    (pool : Finset ℕ) (w : X → ℝ) (hw : ∀ x,0 ≤ w x)
    (F G : Z → X → Finset ℕ → ℂ) :
    (∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖F z x S-G z x S‖^2) ≤
    2*((∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖F z x S‖^2)+
       (∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖G z x S‖^2)) := by
  have hp (z : Z) (x : X) (S : Finset ℕ) :
      ‖F z x S-G z x S‖^2 ≤ 2*(‖F z x S‖^2+‖G z x S‖^2) := by
    have hs := pow_le_pow_left₀ (norm_nonneg (F z x S-G z x S))
      (norm_sub_le (F z x S) (G z x S)) 2
    nlinarith [sq_nonneg (‖F z x S‖-‖G z x S‖)]
  calc
    _ ≤ ∑ z,∑ S ∈ pool.powerset,∑ x,
        2*(w x*‖F z x S‖^2+w x*‖G z x S‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro x hx
      calc
        _ ≤ w x*(2*(‖F z x S‖^2+‖G z x S‖^2)) :=
          mul_le_mul_of_nonneg_left (hp z x S) (hw x)
        _ = _ := by ring
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]

/-- The literal allowed-auxiliary-minus-RAW evolution on the coupled
SMALL, active, numerical seen and OLD carrier has arbitrary-power energy
saving. Both original permutation means and all four endpoint signs remain.
The slot bound is explicit and the density is the same on both sides. -/
theorem eventually_source_original_B26_NODUP_MARKED_SMALL_CLEAN_RAW_MEAN_SAVING434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck Cslots : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck)
    (ell : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
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
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (epsSrc epsTgt : Bool)
      (f : Green64SmallHaar.GroupState SP sm (J+ell) →
        SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val) J ell sizes prime mu
      (sourceOriginalB26NodupMarkedSmallCleanRawMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_MARKED_SMALL_COMPARISON_MEAN_ERROR434
      cfg gamma dscale (Bgoal+2) Cfreq Ck hgamma hd (by linarith) hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_NODUP_MARKED_SMALL_AUX_BAN_MEAN434
    cfg ell q hq hq1 Cslots (Bgoal+2) Cq Cxi,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (2:ℝ)] with L hMain hBanMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ hSlots zeta theta o k ho hZeta hk epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let cmp := sourceOriginalB26NodupMarkedSmallComparisonMean434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f
  let ban := sourceOriginalB26NodupMarkedSmallAuxBanMean434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f
  let energy := sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
    J ell sizes prime mu
  have hCmp := hMain x Y Hprime data SP sm sizes prime sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ zeta theta o k ho hZeta hk epsSrc epsTgt f
  have hBan : energy ban ≤ L^(-(Bgoal+2))*energy f :=
    hBanMain x Y Hprime data SP sm sizes prime hVbig hTbLower
      blockA blockB hDisjoint m hm J hmJ hSlots Q h xi hh hxi hQupper hXi
      zeta theta o k ho epsSrc epsTgt f
  refine ⟨hCmp.1,?_⟩
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (cfg.hv.trans_le (data.hVbig g))
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  have hw (a : A) : 0 ≤ w a :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (hmu g (a g i)).le))
  have hEin : 0 ≤ energy f := by
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro S hS
    exact source_original_B26_active_energy_nonneg434 BP J ell mu hmu
      (fun a => f z.1 a S z.2)
  have hDiff : energy (fun xs a S r => cmp xs a S r-ban xs a S r) ≤
      2*(energy cmp+energy ban) :=
    difference_history_energy
      (Z := Green64SmallHaar.GroupState SP sm (J+ell) ×
        SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime)
      (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) w hw
      (fun z a S => cmp z.1 a S z.2) (fun z a S => ban z.1 a S z.2)
  have hLp : 0 < L := by linarith
  have hFour : (4:ℝ) ≤ L^(2:ℝ) := by rw [Real.rpow_two];nlinarith
  have hBudget : 4*L^(-(Bgoal+2)) ≤ L^(-Bgoal) := by
    calc
      _ ≤ L^(2:ℝ)*L^(-(Bgoal+2)) :=
        mul_le_mul_of_nonneg_right hFour (Real.rpow_nonneg hLp.le _)
      _ = L^(-Bgoal) := by rw [← Real.rpow_add hLp];congr 1;ring
  rw [source_original_B26_NODUP_MARKED_SMALL_MEAN_CLEAN_RAW_DECOMPOSITION434]
  calc
    _ ≤ 2*(energy cmp+energy ban) := hDiff
    _ ≤ 2*(L^(-(Bgoal+2))*energy f+L^(-(Bgoal+2))*energy f) :=
      mul_le_mul_of_nonneg_left (add_le_add hCmp.2 hBan) (by norm_num)
    _ = (4*L^(-(Bgoal+2)))*energy f := by ring
    _ ≤ L^(-Bgoal)*energy f := mul_le_mul_of_nonneg_right hBudget hEin

/-- With J fixed before the L limit, the slot condition follows eventually.
The Fourier and Mellin conductor exponents are chosen before J. -/
theorem eventually_source_original_B26_FIXED_J_NODUP_MARKED_SMALL_CLEAN_RAW_MEAN_SAVING434
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
      (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
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
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (epsSrc epsTgt : Bool)
      (f : Green64SmallHaar.GroupState SP sm (J+ell) →
        SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val) J ell sizes prime mu
      (sourceOriginalB26NodupMarkedSmallCleanRawMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_MARKED_SMALL_CLEAN_RAW_MEAN_SAVING434
      cfg gamma dscale Bgoal Cfreq Ck 1 hgamma hd hGoal hCk ell q hq hq1
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent,eventually_ge_atTop (((J+ell:ℕ):ℝ))] with L hMain hSlots
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm hmJ zeta theta o k ho hZeta hk epsSrc epsTgt f
  exact hMain x Y Hprime data SP sm sizes prime sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ (by simpa only [Real.rpow_one] using hSlots)
    zeta theta o k ho hZeta hk epsSrc epsTgt f


end Green64Analytic.CorrelationSquare

end

end

