module

public import Green64.Library.Correlation.Part062
public import Green64.Library.Weights.Part093
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part089
public import Green64.Library.Weights.UnfilteredEvolutionGhostFullColumn
public import Green64.Library.Weights.Part087
public import Green64.Library.Analysis.Estimates.Part010
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Green64.Library.Weights.Part090
public import Green64.Library.Weights.Part091
public import Green64.Library.Weights.Part092

@[expose] public section

/-!
# Weights / Part094

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEdgeSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- The structural BIG mass bound and fixed source floor give a single
one-step ratio base, chosen before J. -/
def sourceOriginalUnfilteredEdgeRatioBase434 (vmin vmax : ℝ) : ℝ :=
  max 1 (max vmax vmin⁻¹)

/-- Main source theorem at any sufficiently large FIXED J. The explicit
J budget is purely parameter selection and is met by the next theorem.
The actual Option iota SMALL includes S and every Ts. All native RAW and
canonical comparison terms, physical tilt, both OLD gates and true LIST
Nodup are retained. No m<=cfg.tmax, rarity or norm premise is assumed. -/
theorem eventually_source_original_edge_SOURCE_PHASED_BOUNDS434
    (cfg : SourceComparisonFixed434) (m Cq Cxi : ℕ)
    (rho vmax c0 H Ck : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (hvmax : 0 < vmax) (hc0 : 0 < c0) (hH : 0 < H)
    (J : ℕ) (hmJ : m ≤ J)
    (hJ : 2*H+2*sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho
      cfg.vmin (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)+3 ≤
      c0*Real.log ((J+1:ℕ):ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (hQ0 : 0 < Q) (xi : ℝ) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
    let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
      (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
    ∀ (phase : (st : FullPhysicalState SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) cap) →
      FullOrientedSourceChoice SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m cap pats st → ℂ)
      (hphase : ∀ st z,‖phase st z‖ ≤ 1)
      (F : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) → ℂ),
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats (fun _ _ => True) phase cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2))
        zeta theta o k F) ≤
      L^(2*kappa)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F ∧
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats (fun st z => ¬memorySourceCleanChoice SP (fun _ p => p.val) BP
          (fun _ p => p.val) J 1 m cap pats st z)
        phase cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F) ≤
      L^(-(2*H))*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F := by
  let cfg' := sourceOriginalPromotedSmallFixed434 cfg
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_edge_COMPLETE_RARE_ROW434 cfg' 1 Ck cfg.q0 rho
    cfg.hq0 cfg.hq1 hr hr1, eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (8:ℝ),eventually_ge_atTop (Real.exp 1)] with L hRare hVisit hL hLe
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hBigLower
    hHarmonic hVmax hSmallLower blockA blockB hBlocks Q hQ0 xi hxi hQ hXi hA hB hhA hhB
    zeta theta o k ho hk0 hk cap
  let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
  let Kcap := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  let Rv := sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax
  let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin (cfg.C0+1) Rv
  let C := sourceOriginalUnfilteredEdgeBudget434 1 m cfg.q0 rho 2 Vs data.Vbig Kcap
  let D := Rv^((1+m)*Fintype.card G)
  let eps := (Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^(Fintype.card (Option ι))
  dsimp only
  intro phase hphase F
  have hlog : 1 ≤ Real.log L := by simpa using Real.log_le_log (Real.exp_pos 1) hLe
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hVs : ∀ g,0 < Vs g := fun g => cfg.hv.trans_le
    ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hV : ∀ g,0 < data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hbase (g : G) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
      _ g p (hVisit p.val (hBigLower g p.val p.property))).1
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb : 0 < physicalSourceBaseline BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) g p :=
      lt_of_lt_of_le (by norm_num) (hbase g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hb)
  have hmass (g : G) : ∑ p : BP g,mu g p ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP bm cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig g (hV g) (hHarmonic g) (hbase g)).2
  have hRv : 1 ≤ Rv := le_max_left _ _
  have hVR (g : G) : data.Vbig g ≤ Rv := (hVmax g).trans
    ((le_max_left vmax cfg.vmin⁻¹).trans (le_max_right 1 _))
  have hiR (g : G) : (data.Vbig g)⁻¹ ≤ Rv := by
    have hh : (data.Vbig g)⁻¹ ≤ cfg.vmin⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le cfg.hv (data.hVbig g)
    exact hh.trans ((le_max_right vmax cfg.vmin⁻¹).trans (le_max_right 1 _))
  have hK0 := source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi
  have hK := source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
    J 1 m hmJ Q hA hB xi hhA hhB hxi
  have hC : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 1 m cfg.q0 rho 2 Vs data.Vbig Kcap
    cfg.hq0 cfg.hq1 hr1 (by norm_num) hVs hK0
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans hRv) _
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hCB : 0 ≤ C*eps := mul_nonneg hC heps
  have hBig : (Fintype.card G:ℝ) ≤ (cfg.C0+1)*Real.log L := by
    nlinarith only [data.hBigGroups,hlog]
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (cfg.C0+1)*Real.log L := by
    have hh : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [←Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (show (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) by exact_mod_cast hh).trans hBig
  have hPoly : C^2*D ≤ L^(2*kappa) :=
    source_original_edge_CANONICAL_BUDGET_POLYNOMIAL434 blockA blockB 1 m Cq Cxi Q
      cfg.q0 rho cfg.vmin (cfg.C0+1) Rv L xi Vs data.Vbig cfg.hq0 cfg.hq1 hr hr1 cfg.hv
      (by linarith [cfg.hC0]) hRv hL2 hxi
      (source_original_ACTUAL_SMALL_source_bounds434 data).2.2 data.hVbig
      (source_original_ACTUAL_SMALL_group_count434 data hlog) hBig hGroups hQ hXi
  let data' := sourceOriginalPromotedSmallData434 data hlog
  have sep' := source_original_promoted_small_sep434 data hlog sep
  letI : ∀ (g : Option ι) (p : {p : ℕ // p ∈ data'.Ts g}),NeZero p.val := fun g p =>
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  letI : ∀ (g : G) (p : {p : ℕ // p ∈ data'.Tb g}),NeZero p.val := instNZ
  have hrow (K' : SourcePatternK BP J 1 m pats)
      (hK' : ∀ nu aux s t,‖K' nu aux s t‖ ≤ Kcap nu)
      (o' : ℤ) (ho' : o'=1 ∨ o'= -1)
      (st : FullPhysicalState SP sm BP bm (J+1) cap)
      (hOld : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J 1 (Nat.ceil (L^2))
        (physicalFockProjection SP sm BP bm (J+1) cap st)) :
      sourceOriginalMemoryOriginalEPromotionRow434 SP sm BP bm J 1 m cap pats
        cfg.q0 rho Vs data.Vbig mu K' zeta theta o' k st ≤ C*eps := by
    have hh := hRare x Y Hprime data' sep' J m cap st hSmallUpper hBigLower hHarmonic
      pats K' Kcap hK0 hK' zeta theta o' k ho' hk0 hk
    have hOld' : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2) := by
      simpa only [sourceOriginalUnfilteredIdealOLD434,physicalFockProjection,
        Green64Fock.fockMultiset,Multiset.coe_card,List.length_ofFn] using hOld
    have hOldR : ((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ) ≤ (Nat.ceil (L^2):ℝ) := by exact_mod_cast hOld'
    have hden : 0 ≤ ((J+1:ℕ):ℝ)^(Fintype.card (Option ι)) := by positivity
    apply hh.trans
    dsimp only [C,eps,Vs,data',sourceOriginalPromotedSmallData434]
    simp only [Nat.choose_one_right]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hOldR hden) hC
  have hOK := source_original_edge_ORIENTATION_CAP434 BP J 1 m pats K Kcap hK o
  have hneg : -o=1 ∨ -o= -1 := by rcases ho with h | h <;> simp [h]
  have hFull := source_original_edge_LITERAL_PHASED_ENERGY434 SP sm BP bm J 1 m cap pats
    (fun _ _ => True) phase hphase cfg.q0 rho 2 Vs data.Vbig mu cfg.hq0 cfg.hq1 hr hr1
    hVs hV hmu (by norm_num) hmass hHarmonic Rv hRv hVR hiR K (Nat.ceil (L^2)) zeta theta o k
    Kcap hK0 hK F
  have hDirty := source_original_edge_LITERAL_DIRTY_FINITE434 SP sm BP bm J 1 m cap pats phase hphase
    cfg.q0 rho 2 Vs data.Vbig mu cfg.hq0 cfg.hq1 hr hr1 hVs hV hmu (by norm_num) hmass hHarmonic
    Rv hRv hVR hiR K (Nat.ceil (L^2)) zeta theta o k Kcap hK0 hK (C*eps) hCB
    (hrow _ hOK o ho) (hrow _ (fun nu aux s t => hOK nu aux t s) (-o) hneg) F
  have hEn : 0 ≤ sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J 1 cap Vs mu F :=
    Finset.sum_nonneg (fun X hX => mul_nonneg
      (physicalOrbitMass_pos SP sm BP bm (J+1) cap Vs mu hVs hmu X hX).le (sq_nonneg _))
  have hAbs := source_original_edge_DIRTY_SCALAR_BUDGET434 L H kappa c0 C D J
    (Fintype.card (Option ι)) hL hC hD hPoly hSmallLower hJ
  constructor
  · exact hFull.trans (mul_le_mul_of_nonneg_right hPoly hEn)
  · apply hDirty.trans
    convert mul_le_mul_of_nonneg_right hAbs hEn using 1 <;> dsimp only [C,D,eps] <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourcePhasePoly -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The full arbitrary-unit-phase polynomial bank needs no lower bound
on J and no DIRTY-saving choice. It uses the accepted finite energy and
canonical polynomial budget only. The exponent is independent of J. -/
theorem eventually_source_original_root_SOURCE_PHASE_POLY434
    (cfg : SourceComparisonFixed434) (m Cq Cxi : ℕ)
    (rho vmax c0 H Ck : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (hvmax : 0 < vmax) (hc0 : 0 < c0) (hH : 0 < H)
    (J : ℕ) (hmJ : m ≤ J)
:
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (hQ0 : 0 < Q) (xi : ℝ) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
    let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
      (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
    ∀ (phase : (st : FullPhysicalState SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) cap) →
      FullOrientedSourceChoice SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m cap pats st → ℂ)
      (hphase : ∀ st z,‖phase st z‖ ≤ 1)
      (F : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) → ℂ),
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats (fun _ _ => True) phase cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2))
        zeta theta o k F) ≤
      L^(2*kappa)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (8:ℝ),eventually_ge_atTop (Real.exp 1)] with L hVisit hL hLe
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hBigLower
    hHarmonic hVmax hSmallLower blockA blockB hBlocks Q hQ0 xi hxi hQ hXi hA hB hhA hhB
    zeta theta o k ho hk0 hk cap
  let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
  let Kcap := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  let Rv := sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax
  let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin (cfg.C0+1) Rv
  let C := sourceOriginalUnfilteredEdgeBudget434 1 m cfg.q0 rho 2 Vs data.Vbig Kcap
  let D := Rv^((1+m)*Fintype.card G)
  let eps := (Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^(Fintype.card (Option ι))
  dsimp only
  intro phase hphase F
  have hlog : 1 ≤ Real.log L := by simpa using Real.log_le_log (Real.exp_pos 1) hLe
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hVs : ∀ g,0 < Vs g := fun g => cfg.hv.trans_le
    ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hV : ∀ g,0 < data.Vbig g := fun g => cfg.hv.trans_le (data.hVbig g)
  have hbase (g : G) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
      _ g p (hVisit p.val (hBigLower g p.val p.property))).1
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb : 0 < physicalSourceBaseline BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) g p :=
      lt_of_lt_of_le (by norm_num) (hbase g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hb)
  have hmass (g : G) : ∑ p : BP g,mu g p ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP bm cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig g (hV g) (hHarmonic g) (hbase g)).2
  have hRv : 1 ≤ Rv := le_max_left _ _
  have hVR (g : G) : data.Vbig g ≤ Rv := (hVmax g).trans
    ((le_max_left vmax cfg.vmin⁻¹).trans (le_max_right 1 _))
  have hiR (g : G) : (data.Vbig g)⁻¹ ≤ Rv := by
    have hh : (data.Vbig g)⁻¹ ≤ cfg.vmin⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le cfg.hv (data.hVbig g)
    exact hh.trans ((le_max_right vmax cfg.vmin⁻¹).trans (le_max_right 1 _))
  have hK0 := source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi
  have hK := source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
    J 1 m hmJ Q hA hB xi hhA hhB hxi
  have hC : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 1 m cfg.q0 rho 2 Vs data.Vbig Kcap
    cfg.hq0 cfg.hq1 hr1 (by norm_num) hVs hK0
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans hRv) _
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hCB : 0 ≤ C*eps := mul_nonneg hC heps
  have hBig : (Fintype.card G:ℝ) ≤ (cfg.C0+1)*Real.log L := by
    nlinarith only [data.hBigGroups,hlog]
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (cfg.C0+1)*Real.log L := by
    have hh : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [←Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (show (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) by exact_mod_cast hh).trans hBig
  have hPoly : C^2*D ≤ L^(2*kappa) :=
    source_original_edge_CANONICAL_BUDGET_POLYNOMIAL434 blockA blockB 1 m Cq Cxi Q
      cfg.q0 rho cfg.vmin (cfg.C0+1) Rv L xi Vs data.Vbig cfg.hq0 cfg.hq1 hr hr1 cfg.hv
      (by linarith [cfg.hC0]) hRv hL2 hxi
      (source_original_ACTUAL_SMALL_source_bounds434 data).2.2 data.hVbig
      (source_original_ACTUAL_SMALL_group_count434 data hlog) hBig hGroups hQ hXi
  have hFull := source_original_edge_LITERAL_PHASED_ENERGY434 SP sm BP bm J 1 m cap pats
    (fun _ _ => True) phase hphase cfg.q0 rho 2 Vs data.Vbig mu cfg.hq0 cfg.hq1 hr hr1
    hVs hV hmu (by norm_num) hmass hHarmonic Rv hRv hVR hiR K (Nat.ceil (L^2)) zeta theta o k
    Kcap hK0 hK F
  have hEn : 0 ≤ sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J 1 cap Vs mu F :=
    Finset.sum_nonneg (fun X hX => mul_nonneg
      (physicalOrbitMass_pos SP sm BP bm (J+1) cap Vs mu hVs hmu X hX).le (sq_nonneg _))
  exact hFull.trans (mul_le_mul_of_nonneg_right hPoly hEn)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeFinal -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A fixed J chosen after m and kappa; independent of L. -/
theorem source_original_edge_CHOOSE_J434 (m : ℕ) (H kappa c0 : ℝ) (hc0 : 0 < c0) :
    ∃ J : ℕ,m ≤ J ∧ 2*H+2*kappa+3 ≤ c0*Real.log ((J+1:ℕ):ℝ) := by
  let J := sourceOriginalMemoryRareSlotChoice434 m c0 0 1 (2*H+2*kappa)
  have hh := source_original_memory_rare_slot_choice434 m 1 (by norm_num) c0 0 1 (2*H+2*kappa) hc0
  refine ⟨J,hh.1,?_⟩
  simpa only [Nat.choose_one_right,zero_mul,add_zero] using hh.2

/-- Exact ORIGINAL operators, not a norm wrapper: phase=1 of the proved
literal source theorem. The displayed statement is the expected-type audit
for both original definitions in the SAME plain physical energy. -/
theorem eventually_source_original_edge_SOURCE_BOUNDS434
    (cfg : SourceComparisonFixed434) (m Cq Cxi : ℕ)
    (rho vmax c0 H Ck : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (hvmax : 0 < vmax) (hc0 : 0 < c0) (hH : 0 < H)
    (J : ℕ) (hmJ : m ≤ J)
    (hJ : 2*H+2*sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho
      cfg.vmin (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)+3 ≤
      c0*Real.log ((J+1:ℕ):ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (hQ0 : 0 < Q) (xi : ℝ) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
    let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
      (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
    ∀ (F : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) → ℂ),
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2))
        zeta theta o k F) ≤
      L^(2*kappa)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F ∧
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedDirty434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F) ≤
      L^(-(2*H))*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F := by
  filter_upwards [eventually_source_original_edge_SOURCE_PHASED_BOUNDS434 cfg m Cq Cxi
    rho vmax c0 H Ck hr hr1 hvmax hc0 hH J hmJ hJ] with L hMain
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hBigLower
    hHarmonic hVmax hSmallLower blockA blockB hBlocks Q hQ0 xi hxi hQ hXi hA hB hhA hhB
    zeta theta o k ho hk0 hk cap
  dsimp only
  intro F
  have hh := hMain x Y Hprime data sep hSmallUpper hBigLower hHarmonic hVmax hSmallLower
    blockA blockB hBlocks Q hQ0 xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk cap
  dsimp only at hh
  have h := hh (fun _ _ => 1) (by intro st z; simp) F
  simpa only [sourceOriginalUnfilteredIdealOrbitEnergy434,
    source_original_edge_PHASE_ONE_FULL434,source_original_edge_PHASE_ONE_DIRTY434] using h

/-- Desired parameter order: fixed m/precisions, then fixed J, then L. -/
theorem eventually_source_original_edge_CHOSEN_ORIGINAL_BOUNDS434
    (cfg : SourceComparisonFixed434) (m Cq Cxi : ℕ)
    (rho vmax c0 H Ck : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (hvmax : 0 < vmax) (hc0 : 0 < c0) (hH : 0 < H) :
    ∃ (J : ℕ) (hmJ : m ≤ J),
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (hQ0 : 0 < Q) (xi : ℝ) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q hA hB xi
    let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
      (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
    ∀ (F : FullPhysicalOutput SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) → ℂ),
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2))
        zeta theta o k F) ≤
      L^(2*kappa)*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F ∧
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedDirty434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F) ≤
      L^(-(2*H))*sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP
        (fun _ p => p.val) J 1 cap Vs mu F := by
  obtain ⟨J,hmJ,hJ⟩ := source_original_edge_CHOOSE_J434 m H
    (sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin (cfg.C0+1)
      (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)) c0 hc0
  exact ⟨J,hmJ,eventually_source_original_edge_SOURCE_BOUNDS434 cfg m Cq Cxi rho vmax c0 H Ck
    hr hr1 hvmax hc0 hH J hmJ hJ⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Finite positive weighted Cauchy--Schwarz. The column premise is a tested
density marginal; the actual physical instance is proved in the next module. -/
theorem source_original_evolution_weighted_pair434
    {A : Type} [Fintype A]
    (mu w : A → ℝ) (hm : ∀ x,0 ≤ mu x) (hw : ∀ x,0 < w x)
    (P : A → A → ℝ) (hP : ∀ x y,0 ≤ P x y) (C : ℝ) (hC : 0 ≤ C)
    (F H raw : A → ℂ)
    (hr : ∀ x,∑ y,P x y*w y ≤ C*w x)
    (hc : (∑ x,∑ y,mu x*w x*P x y*(‖F y‖^2/w y)) ≤
      C*(∑ y,mu y*‖F y‖^2))
    (hraw : ∀ x,‖raw x‖ ≤ ∑ y,P x y*‖F y‖) :
    ‖∑ x,(mu x:ℂ)*star (H x)*raw x‖^2 ≤
      C^2*(∑ x,mu x*‖H x‖^2)*(∑ y,mu y*‖F y‖^2) := by
  let r := fun z : A×A => mu z.1*P z.1 z.2*‖H z.1‖*‖F z.2‖
  let f := fun z : A×A => mu z.1*P z.1 z.2*(w z.2/w z.1)*‖H z.1‖^2
  let g := fun z : A×A => mu z.1*P z.1 z.2*(w z.1/w z.2)*‖F z.2‖^2
  have hf0 (z : A×A) : 0 ≤ f z := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hm _) (hP _ _))
      (div_nonneg (hw _).le (hw _).le)) (sq_nonneg _)
  have hg0 (z : A×A) : 0 ≤ g z := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hm _) (hP _ _))
      (div_nonneg (hw _).le (hw _).le)) (sq_nonneg _)
  have heq (z : A×A) : (r z)^2 ≤ f z*g z := by
    dsimp only [r,f,g]
    have hx := ne_of_gt (hw z.1)
    have hy := ne_of_gt (hw z.2)
    field_simp
    ring_nf
    exact le_rfl
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset (A×A))) (r := r) (f := f) (g := g)
    (fun z _ => hf0 z) (fun z _ => hg0 z) (fun z _ => heq z)
  have hf : (∑ z : A×A,f z) ≤ C*(∑ x,mu x*‖H x‖^2) := by
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have he :
        (∑ y,mu x*P x y*(w y/w x)*‖H x‖^2) =
        (mu x*‖H x‖^2/w x)*(∑ y,P x y*w y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    change (∑ y,mu x*P x y*(w y/w x)*‖H x‖^2) ≤ _
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (hr x)
      (div_nonneg (mul_nonneg (hm x) (sq_nonneg ‖H x‖)) (hw x).le)
    convert hh using 1
    have hx := ne_of_gt (hw x)
    field_simp
  have hg : (∑ z : A×A,g z) ≤ C*(∑ y,mu y*‖F y‖^2) := by
    rw [Fintype.sum_prod_type]
    convert hc using 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [g]
    ring
  have ht : ‖∑ x,(mu x:ℂ)*star (H x)*raw x‖ ≤ ∑ z : A×A,r z := by
    calc
      _ ≤ ∑ x,‖(mu x:ℂ)*star (H x)*raw x‖ := norm_sum_le _ _
      _ = ∑ x,mu x*‖H x‖*‖raw x‖ := by
        apply Finset.sum_congr rfl
        intro x _
        simp [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hm x)]
      _ ≤ ∑ x,mu x*‖H x‖*(∑ y,P x y*‖F y‖) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hraw x)
          (mul_nonneg (hm x) (norm_nonneg _)))
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        dsimp only [r]
        ring
  have hboth := mul_le_mul hf hg
    (Finset.sum_nonneg (fun z _ => hg0 z))
    (mul_nonneg hC (Finset.sum_nonneg (fun x _ => mul_nonneg (hm x) (sq_nonneg ‖H x‖))))
  calc
    _ ≤ (∑ z : A×A,r z)^2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ z : A×A,f z)*(∑ z : A×A,g z) := hcs
    _ ≤ (C*(∑ x,mu x*‖H x‖^2))*(C*(∑ y,mu y*‖F y‖^2)) := hboth
    _ = _ := by ring

/-- Finite integration of a density-column estimate over the actual image
support; no conditional distribution or renormalization is introduced. -/
theorem source_original_evolution_test_columns434
    {A O : Type} [Fintype A] [DecidableEq O]
    (proj : A → O) (L : A → A → ℝ) (R : A → ℝ) (C : ℝ)
    (hc : ∀ Y : O,
      (∑ x,∑ y,L x y*(if proj y=Y then 1 else 0)) ≤
        C*(∑ y,R y*(if proj y=Y then 1 else 0)))
    (H : O → ℝ) (hH : ∀ Y,0 ≤ H Y) :
    (∑ x,∑ y,L x y*H (proj y)) ≤ C*(∑ y,R y*H (proj y)) := by
  let S := (Finset.univ : Finset A).image proj
  have hs (y : A) : proj y ∈ S := Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩
  have he (f : A → ℝ) :
      (∑ Y ∈ S,(∑ y,f y*(if proj y=Y then 1 else 0))*H Y) =
      ∑ y,f y*H (proj y) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [hs y,if_true]
  have heL :
      (∑ Y ∈ S,(∑ x,∑ y,L x y*(if proj y=Y then 1 else 0))*H Y) =
      ∑ x,∑ y,L x y*H (proj y) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simpa only [Finset.sum_mul] using he (L x)
  rw [←heL,←he R]
  calc
    _ ≤ ∑ Y ∈ S,(C*(∑ y,R y*(if proj y=Y then 1 else 0)))*H Y :=
      Finset.sum_le_sum (fun Y _ => mul_le_mul_of_nonneg_right (hc Y) (hH Y))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostEnergyBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Exact pullback of the specified plain physical orbit energy to ordered
factorial representatives, including every repeated OLD atom. -/
theorem source_original_evolution_ORBIT_energy_pullback434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (F : Output → ℂ) :
    (∑ x : State,fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x*
      ‖F (physicalFockProjection SP sm BP bm (J+ell) cap x)‖^2) =
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  letI : DecidableEq Output := Classical.decEq _
  let proj := physicalFockProjection SP sm BP bm (J+ell) cap
  let mass := fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu
  let S := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  have hx (x : State) : proj x ∈ S := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  have he (x : State) :
      (∑ Y ∈ S,if proj x=Y then mass x*‖F (proj x)‖^2 else 0) =
      mass x*‖F (proj x)‖^2 := by
    simpa only [hx x,ite_true] using
      (Finset.sum_ite_eq S (proj x) (fun _ : Output => mass x*‖F (proj x)‖^2))
  change (∑ x : State,mass x*‖F (proj x)‖^2)=_
  calc
    _ = ∑ x : State,∑ Y ∈ S,if proj x=Y then mass x*‖F (proj x)‖^2 else 0 :=
      Finset.sum_congr rfl (fun x _ => (he x).symm)
    _ = ∑ Y ∈ S,∑ x : State,if proj x=Y then mass x*‖F (proj x)‖^2 else 0 :=
      Finset.sum_comm
    _ = _ := by
      unfold sourceOriginalUnfilteredIdealOrbitEnergy434 physicalOrbitMass
      apply Finset.sum_congr rfl
      intro Y _
      rw [Finset.sum_mul,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      change (if proj x=Y then mass x*‖F (proj x)‖^2 else 0) =
        (if proj x=Y then mass x*‖F Y‖^2 else 0)
      by_cases h : proj x=Y
      · simp only [h,ite_true]
      · simp only [h,ite_false]

theorem source_original_evolution_ORBIT_inner_self434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (F : Output → ℂ) :
    physicalSymmetricInner SP sm BP bm (J+ell) cap Vs mu F F =
    (sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F:ℂ) := by
  unfold physicalSymmetricInner sourceOriginalUnfilteredIdealOrbitEnergy434
  push_cast
  apply Finset.sum_congr rfl
  intro Y _
  rw [mul_assoc,mul_comm (star (F Y)) (F Y)]
  rw [show F Y*star (F Y)=((‖F Y‖:ℝ):ℂ)^2 from Complex.mul_conj' (F Y)]

/-- Exact same-density conversion of a derived bilinear bound to the
specified physical orbit energy. No invariance of the raw row is assumed. -/
theorem source_original_evolution_ORBIT_energy_from_pair434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (C : ℝ) (F : Output → ℂ) (raw : State → ℂ)
    (hpair : ∀ H : Output → ℂ,
      ‖∑ x : State,(fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*
        star (H (physicalFockProjection SP sm BP bm (J+ell) cap x))*raw x‖^2 ≤
      C^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu H*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu raw) ≤
    C^2*sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let T := fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu raw
  let E := sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
  have hE (H : Output → ℂ) : 0 ≤ E H := by
    unfold E sourceOriginalUnfilteredIdealOrbitEnergy434
    exact Finset.sum_nonneg (fun Y hY => mul_nonneg
      (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu Y hY).le
      (sq_nonneg _))
  have he := fullPhysicalOrbitAverage_pairing SP sm BP bm (J+ell) cap Vs mu hVs hmu T raw
  rw [source_original_evolution_ORBIT_inner_self434] at he
  change (E T:ℂ)=(∑ x : State,(fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*
    star (T (physicalFockProjection SP sm BP bm (J+ell) cap x))*raw x) at he
  have hp := hpair T
  rw [←he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hE T)] at hp
  change E T ≤ C^2*E F
  by_cases hz : E T=0
  · rw [hz]
    exact mul_nonneg (sq_nonneg _) (hE F)
  · have hpos : 0 < E T := lt_of_le_of_ne (hE T) (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := E T) _ hpos
    nlinarith only [hp]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostPhysicalPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Derived bilinear estimate for the literal full physical G positive
majorant. All row and column estimates have been discharged on that carrier. -/
theorem source_original_evolution_PHYSICAL_G_pair434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (F H : Output → ℂ) (raw : State → ℂ)
    (hraw : ∀ x,‖raw x‖ ≤
      ∑ y : State,∑ c : FullGhostWitness SP sm BP bm (J+ell) cap x,
        (2:ℝ)^(∑ g,(c g).2.1.val)*
          ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c‖*
          ‖F (physicalFockProjection SP sm BP bm (J+ell) cap y)‖) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ‖∑ x : State,(fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*
      star (H (physicalFockProjection SP sm BP bm (J+ell) cap x))*raw x‖^2 ≤
      (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu H*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  let C := Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)
  let proj := physicalFockProjection SP sm BP bm (J+ell) cap
  let mass := fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu
  let wt := fun x : State => w^(∑ g,((x.2 g).2).1.val)
  let P := fun x y : State =>
    ∑ c : FullGhostWitness SP sm BP bm (J+ell) cap x,
      (2:ℝ)^(∑ g,(c g).2.1.val)*
        ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c‖
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  have hwt (x : State) : 0 < wt x := pow_pos hw.1 _
  have hmass0 (x : State) : 0 ≤ mass x :=
    (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu x).le
  have hP (x y : State) : 0 ≤ P x y :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) (norm_nonneg _))
  have hrow (x : State) : (∑ y,P x y*wt y) ≤ C*wt x := by
    dsimp only [P]
    simp_rw [Finset.sum_mul]
    exact source_original_evolution_PHYSICAL_G_gamma_row434 SP sm BP bm (J+ell) cap
      q rho W N i hq hq1 hr hW hg V hV hVW mu (fun g p => (hmu g p).le) hmass x
  have hcolumn (Y : Output) :
      (∑ x : State,∑ y : State,(mass x*wt x*P x y)*(if proj y=Y then 1 else 0)) ≤
      C*(∑ y : State,(mass y*wt y)*(if proj y=Y then 1 else 0)) := by
    have hh := source_original_evolution_PHYSICAL_G_gamma_column434
      SP sm BP bm (J+ell) cap q rho W N i hq hq1 hr hW hg
      Vs hVs V hV hVW mu hmu hmass Y
    dsimp only at hh
    rw [mul_assoc,←source_original_evolution_PHYSICAL_weighted_fibre434
      SP sm BP bm (J+ell) cap Vs mu w Y] at hh
    exact hh
  have htest := @source_original_evolution_test_columns434 State Output
    inferInstance (fun X Y : Output => inferInstance) proj
    (fun x y : State => mass x*wt x*P x y) (fun y => mass y*wt y) C hcolumn
    (fun Y : Output => ‖F Y‖^2/(w^(∑ g,((Y.2 g).2).card)))
    (fun Y => div_nonneg (sq_nonneg _) (pow_nonneg hw.1.le _))
  have hp (y : State) : w^(∑ g,(((proj y).2 g).2).card)=wt y := by
    rw [source_original_evolution_projection_OLD434]
  simp_rw [hp] at htest
  have hc :
      (∑ x : State,∑ y : State,mass x*wt x*P x y*(‖F (proj y)‖^2/wt y)) ≤
      C*(∑ y : State,mass y*‖F (proj y)‖^2) := by
    convert htest using 1
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have hy := ne_of_gt (hwt y)
    field_simp
  have hraw' (x : State) : ‖raw x‖ ≤ ∑ y,P x y*‖F (proj y)‖ := by
    dsimp only [P]
    simp_rw [Finset.sum_mul]
    exact hraw x
  have hh := source_original_evolution_weighted_pair434 mass wt hmass0 hwt P hP C
    (Real.exp_pos _).le (fun x => F (proj x)) (fun x => H (proj x)) raw hrow hc hraw'
  rw [source_original_evolution_ORBIT_energy_pullback434,
    source_original_evolution_ORBIT_energy_pullback434] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The original physical G row is dominated by its actual doubled-birth
positive witness kernel, before orbit averaging. -/
theorem source_original_evolution_ORIGINAL_G_majorant434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : Output → ℂ) (x : State) :
    ‖physicalVisitGRow SP sm BP bm (J+ell) cap q rho N i V mu
      (fun y => F (physicalFockProjection SP sm BP bm (J+ell) cap y)) x‖ ≤
    ∑ y : State,∑ c : FullGhostWitness SP sm BP bm (J+ell) cap x,
      (2:ℝ)^(∑ g,(c g).2.1.val)*
        ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c‖*
        ‖F (physicalFockProjection SP sm BP bm (J+ell) cap y)‖ := by
  unfold physicalVisitGRow
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro y _
  rw [norm_mul,←physicalGWitnessKernel_eq_source SP sm BP bm (J+ell) cap
    q rho N i V mu x y]
  unfold physicalGWitnessKernel
  calc
    _ ≤ (∑ c : FullGhostWitness SP sm BP bm (J+ell) cap x,
        ‖physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c‖)*
        ‖F (physicalFockProjection SP sm BP bm (J+ell) cap y)‖ :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro c _
      have hb : (1:ℝ) ≤ 2^(∑ g,(c g).2.1.val) :=
        one_le_pow₀ (by norm_num)
      have ht := mul_le_mul_of_nonneg_right hb
        (norm_nonneg (physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (norm_nonneg _)

/-- Actual complete physicalSymmetricVisitGRow energy in the exact plain
physical orbit density. Gamma is independent of all finite OLD caps and J. -/
theorem source_original_evolution_ORIGINAL_G_ENERGY434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2) (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  apply source_original_evolution_ORBIT_energy_from_pair434 SP sm BP bm J ell cap
    Vs hVs mu hmu
  intro H
  exact source_original_evolution_PHYSICAL_G_pair434 SP sm BP bm J ell cap
    q rho W N i hq hq1 hr hW hg Vs hVs V hV hVW mu hmu hmass F H _
    (source_original_evolution_ORIGINAL_G_majorant434 SP sm BP bm J ell cap q rho N i V mu F)

/-- The literal local fresh LIST Nodup row, with every original witness
phase bounded by 2 per birth, has the same complete physical energy bound.
This is an absolute estimate; no CLEAN cancellation is asserted for phases. -/
theorem source_original_evolution_SEEN_ERASED_G_ENERGY434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phase : (x : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hphase : ∀ x c,‖phase x c‖ ≤ (2:ℝ)^(∑ g,(c g).2.1.val))
    (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
        q rho N i Vs V mu phase F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  unfold sourceOriginalUnfilteredEvolutionSeenErasedG434
  apply source_original_evolution_ORBIT_energy_from_pair434 SP sm BP bm J ell cap
    Vs hVs mu hmu
  intro H
  apply source_original_evolution_PHYSICAL_G_pair434 SP sm BP bm J ell cap
    q rho W N i hq hq1 hr hW hg Vs hVs V hV hVW mu hmu hmass F H
  intro x
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro y _
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · rw [norm_mul,norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hphase x c)
      (norm_nonneg (physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y c))
    have ht := mul_le_mul_of_nonneg_right hh
      (norm_nonneg (F (physicalFockProjection SP sm BP bm (J+ell) cap y)))
    convert ht using 1 <;> ring
  · simp only [norm_zero]
    positivity
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostQuantitativeEnergy -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Original source regime: the actual complete symmetric G and the literal
seen-erased LIST-filtered G have squared energy bound L^(2 Cv), where
Cv=4 W w C0/rho depends only on fixed q,rho,W,C0. The eventual threshold is
uniform in J, ell, all OLD caps and all independent SMALL/BIG group types. -/
theorem eventually_source_original_evolution_TILTED_G_ENERGY434
    (c q rho W C0 : ℝ) (hc : 0 < c)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hW : 1 ≤ W) (hg : Real.sqrt q/rho^2 < 1) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (J ell : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
      (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hcount : (Fintype.card BG:ℝ) ≤ C0*Real.log L)
      (i : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ),
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP bm q N V
    (sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
        (L^(4*W*w*C0/rho))^2*
          sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) ∧
    (∀ (phase : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
        FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
      (hphase : ∀ x z,‖phase x z‖ ≤ (2:ℝ)^(∑ g,(z g).2.1.val)),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
          q rho N i Vs V mu phase F) ≤
      (L^(4*W*w*C0/rho))^2*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc,
    eventually_gt_atTop (0:ℝ)] with L hVisit hL
  intro SG BG instSG instDSG instBG instDBG SP instSP instDSP sm instNZS
    BP instBP instDBP bm instNZB J ell cap Vs V hVs hV hVW hHarmonic hBig hcount i F
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hb (g : BG) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hVisit _ (hBig g p))).1
  have hmu (g : BG) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hbase : 0 < physicalSourceBaseline BP bm q N g p :=
      lt_of_lt_of_le (by norm_num) (hb g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hbase)
  have hmass (g : BG) : (∑ p,mu g p) ≤ 2 :=
    (source_original_memory_physical_tilt_mass_two434 BP bm q N V g (hV g)
      (hHarmonic g) (hb g)).2
  have hp := source_original_evolution_GAMMA_polynomial434 L W w rho C0
    (Fintype.card BG) hL (zero_le_one.trans hW) hw.1.le hr hcount
  have hp2 := pow_le_pow_left₀ (Real.exp_pos _).le hp 2
  have hE : 0 ≤ sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
    unfold sourceOriginalUnfilteredIdealOrbitEnergy434
    exact Finset.sum_nonneg (fun Y hY => mul_nonneg
      (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu Y hY).le
      (sq_nonneg _))
  constructor
  · exact (source_original_evolution_ORIGINAL_G_ENERGY434 SP sm BP bm J ell cap
      q rho W N i hq hq1 hr hW hg Vs hVs V (fun g => (hV g).le) hVW
      mu hmu hmass F).trans (mul_le_mul_of_nonneg_right hp2 hE)
  · intro phase hphase
    exact (source_original_evolution_SEEN_ERASED_G_ENERGY434 SP sm BP bm J ell cap
      q rho W N i hq hq1 hr hW hg Vs hVs V (fun g => (hV g).le) hVW
      mu hmu hmass phase hphase F).trans (mul_le_mul_of_nonneg_right hp2 hE)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionAudit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


/-- Independent explicit type boundary for the original physical row. -/
theorem source_original_evolution_ORIGINAL_G_ENERGY434_expected_type
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2) (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  exact source_original_evolution_ORIGINAL_G_ENERGY434 SP sm BP bm J ell cap q rho W N i hq hq1 hr hW hg Vs hVs V hV hVW mu hmu hmass F

/-- Independent explicit type boundary for the original physical row. -/
theorem source_original_evolution_SEEN_ERASED_G_ENERGY434_expected_type
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phase : (x : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hphase : ∀ x c,‖phase x c‖ ≤ (2:ℝ)^(∑ g,(c g).2.1.val))
    (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
        q rho N i Vs V mu phase F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  exact source_original_evolution_SEEN_ERASED_G_ENERGY434 SP sm BP bm J ell cap q rho W N i hq hq1 hr hW hg Vs hVs V hV hVW mu hmu hmass phase hphase F

theorem eventually_source_original_evolution_TILTED_G_ENERGY434_expected_type
    (c q rho W C0 : ℝ) (hc : 0 < c)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hW : 1 ≤ W) (hg : Real.sqrt q/rho^2 < 1) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (J ell : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
      (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hcount : (Fintype.card BG:ℝ) ≤ C0*Real.log L)
      (i : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ),
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP bm q N V
    (sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
        (L^(4*W*w*C0/rho))^2*
          sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) ∧
    (∀ (phase : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
        FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
      (hphase : ∀ x z,‖phase x z‖ ≤ (2:ℝ)^(∑ g,(z g).2.1.val)),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
          q rho N i Vs V mu phase F) ≤
      (L^(4*W*w*C0/rho))^2*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) := by
  exact eventually_source_original_evolution_TILTED_G_ENERGY434 c q rho W C0 hc hq hq1 hr hW hg

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionOriginalParameters -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)


/-- The original quarter-root parameter condition implies precisely the
positive damping-gap condition used in the finite calculation. -/
theorem source_original_evolution_QUARTER_ROOT_gap434
    (q rho : ℝ) (hq : 0 ≤ q) (hquarter : q^(1/4:ℝ) < rho) :
    0 < rho ∧ Real.sqrt q/rho^2 < 1 := by
  have h0 : 0 ≤ q^(1/4:ℝ) := by positivity
  have hr : 0 < rho := lt_of_le_of_lt h0 hquarter
  have hs : (q^(1/4:ℝ))^2=Real.sqrt q := by
    rw [←Real.rpow_mul_natCast hq (1/4:ℝ) 2,Real.sqrt_eq_rpow]
    norm_num
  have hp : 0 < (rho-q^(1/4:ℝ))*(rho+q^(1/4:ℝ)) :=
    mul_pos (sub_pos.mpr hquarter) (by linarith)
  refine ⟨hr,(div_lt_one (by positivity : 0 < rho^2)).mpr ?_⟩
  nlinarith only [hp,hs]

theorem source_original_evolution_ORIGINAL_G_ENERGY434_original_parameters
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho)
    (hr1 : rho < 1) (hW : 1 ≤ W)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2) (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  have hh := source_original_evolution_QUARTER_ROOT_gap434 q rho hq.le hquarter
  exact source_original_evolution_ORIGINAL_G_ENERGY434 SP sm BP bm J ell cap q rho W N i hq.le hq1.le hh.1 hW hh.2 Vs hVs V hV hVW mu hmu hmass F

theorem source_original_evolution_SEEN_ERASED_G_ENERGY434_original_parameters
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho)
    (hr1 : rho < 1) (hW : 1 ≤ W)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phase : (x : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hphase : ∀ x c,‖phase x c‖ ≤ (2:ℝ)^(∑ g,(c g).2.1.val))
    (F : Output → ℂ) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
        q rho N i Vs V mu phase F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  have hh := source_original_evolution_QUARTER_ROOT_gap434 q rho hq.le hquarter
  exact source_original_evolution_SEEN_ERASED_G_ENERGY434 SP sm BP bm J ell cap q rho W N i hq.le hq1.le hh.1 hW hh.2 Vs hVs V hV hVW mu hmu hmass phase hphase F

theorem eventually_source_original_evolution_TILTED_G_ENERGY434_original_parameters
    (c q rho W C0 : ℝ) (hc : 0 < c)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho)
    (hr1 : rho < 1) (hW : 1 ≤ W) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (J ell : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
      (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hBig : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hcount : (Fintype.card BG:ℝ) ≤ C0*Real.log L)
      (i : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ),
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP bm q N V
    (sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
        (L^(4*W*w*C0/rho))^2*
          sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) ∧
    (∀ (phase : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
        FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
      (hphase : ∀ x z,‖phase x z‖ ≤ (2:ℝ)^(∑ g,(z g).2.1.val)),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
          q rho N i Vs V mu phase F) ≤
      (L^(4*W*w*C0/rho))^2*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F) := by
  have hh := source_original_evolution_QUARTER_ROOT_gap434 q rho hq.le hquarter
  exact eventually_source_original_evolution_TILTED_G_ENERGY434 c q rho W C0 hc hq.le hq1.le hh.1 hW hh.2

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootParameters -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The prescribed original w meets the full-rank source suffix condition.
No additional parameter regularity is assumed. -/
theorem source_original_global_root_ORIGINAL_W_CONTROL434
    (q rho W : ℝ) (hq : 0 ≤ q) (hquarter : q^(1/4:ℝ)< rho) (hW : 1 ≤ W) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    1 ≤ w ∧ 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1 := by
  dsimp only
  have hg := source_original_evolution_QUARTER_ROOT_gap434 q rho hq hquarter
  have ht : 0 < 1-Real.sqrt q/rho^2 := sub_pos.mpr hg.2
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  have hw : 1 ≤ w := le_max_left _ _
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hbig : 4*W ≤ w*(rho*(1-Real.sqrt q/rho^2)) :=
    (div_le_iff₀ (mul_pos hg.1 ht)).mp (le_max_right _ _)
  have hsmall : 1/(rho*w) ≤ 1-Real.sqrt q/rho^2 := by
    apply (div_le_iff₀ (mul_pos hg.1 hw0)).mpr
    nlinarith
  exact ⟨hw,by linarith⟩

/-- Original group separation supplies the numerical injectivity required
by moving OLD removal, including the dependent BIG subtype. -/
theorem source_original_global_root_BIG_INJECTIVE434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data) :
    Function.Injective (fun z : Sigma (fun g => {p : ℕ // p∈data.Tb g}) => z.2.val) := by
  rintro ⟨g,p⟩ ⟨h,q⟩ he
  change p.val=q.val at he
  have hgh : g=h := sep.hBB g h p.val p.property (he.symm ▸ q.property)
  cases hgh
  have hpq : p=q := Subtype.ext he
  cases hpq
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootPrefactors -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Original G exponential becomes the early fixed polynomial exponent. -/
theorem source_original_global_root_GAMMA_POLY434
    (L W w rho C0 : ℝ) (n : ℕ) (hL : 0<L) (hW : 0≤W) (hw : 0≤w) (hr : 0< rho)
    (hn : (n:ℝ)≤C0*Real.log L) :
    Real.exp (4*W*w*(n:ℝ)/rho)≤L^(4*W*w*C0/rho) := by
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hn (show 0≤4*W*w/rho by positivity)
  convert hh using 1 <;> ring

/-- Charge the whole vacuum once; late Cv/N is absorbed by N>=Cv. -/
theorem source_original_global_root_PREFACTOR434
    (L Cv Bvac Gamma : ℝ) (beta : ℂ) (N : ℕ)
    (hL : 1≤L) (hCv : Cv≤(N:ℝ)) (hB : 0≤Bvac) (hG : 0≤Gamma)
    (hbeta : ‖beta‖≤1) (hBbound : Bvac≤L^(N:ℝ)) (hGbound : Gamma≤L^Cv) :
    ‖beta‖*Bvac*Gamma^(N+1)≤L^((Cv+2)*(N:ℝ)) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hg : (L^Cv)^(N+1)=L^(Cv*((N+1:ℕ):ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
  calc
    _ ≤ (1*L^(N:ℝ))*(L^Cv)^(N+1) := by
      exact mul_le_mul (mul_le_mul hbeta hBbound hB (by norm_num))
        (pow_le_pow_left₀ hG hGbound _) (pow_nonneg hG _) (by positivity)
    _ = L^((N:ℝ)+Cv*((N+1:ℕ):ℝ)) := by rw [one_mul,hg,←Real.rpow_add hLp]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      push_cast
      nlinarith

/-- The marked-owner inflation has a fixed exponent independent of J. -/
theorem source_original_global_root_MARKED_POLY434
    (L kappa S : ℝ) (hL : 1≤L) :
    max 1 (L^kappa/L^(-S))≤L^(max 0 (kappa+S)) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  apply max_le
  · exact Real.one_le_rpow hL (le_max_left _ _)
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos hLp (-S))).mpr
    rw [←Real.rpow_add hLp]
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith [le_max_right (0:ℝ) (kappa+S)]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionFinalAudit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)



/-- Final explicit original-operator boundary with the requested W=max(1,vmax). -/
theorem source_original_evolution_FINAL_G_ENERGY434
    (q rho vmax : ℝ) (N i : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho)
    (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2) (F : Output → ℂ) :
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalSymmetricVisitGRow SP sm BP bm (J+ell) cap q rho N i Vs V mu F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  exact source_original_evolution_ORIGINAL_G_ENERGY434_original_parameters
    SP sm BP bm J ell cap q rho (max 1 vmax) N i hq hq1 hquarter hr1
    (le_max_left _ _) Vs hVs V hV
    (fun g => (hVW g).trans (le_max_right _ _)) mu hmu hmass F

theorem source_original_evolution_FINAL_SEEN_ERASED_G_ENERGY434
    (q rho vmax : ℝ) (N i : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hquarter : q^(1/4:ℝ) < rho)
    (hr1 : rho < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ vmax)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (phase : (x : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (hphase : ∀ x c,‖phase x c‖ ≤ (2:ℝ)^(∑ g,(c g).2.1.val))
    (F : Output → ℂ) :
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
        q rho N i Vs V mu phase F) ≤
    (Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho))^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  exact source_original_evolution_SEEN_ERASED_G_ENERGY434_original_parameters
    SP sm BP bm J ell cap q rho (max 1 vmax) N i hq hq1 hquarter hr1
    (le_max_left _ _) Vs hVs V hV
    (fun g => (hVW g).trans (le_max_right _ _)) mu hmu hmass phase hphase F

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealTiltError -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern G J m)
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns

def sourceOriginalUnfilteredIdealTiltCorrectionK434
    (r : (g : G) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns) :
    SourcePatternK BP J ell m patterns :=
  fun nu aux s t =>
    ((sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m (patterns nu) r s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _):ℂ)-1)*K nu aux s t

theorem source_original_unfiltered_ideal_REAL_EDGE_SCALAR434
    (a : ℝ) (K : ℂ) (zeta theta : ℝ) (D : ℕ) (o k : ℤ) :
    originalEdgeScalar ((a:ℂ)*K) zeta theta D o k =
      (a:ℂ)*originalEdgeScalar K zeta theta D o k := by
  have hstar : star (a:ℂ)=(a:ℂ) := Complex.conj_ofReal a
  unfold originalEdgeScalar originalOrientedKernel
  split_ifs
  · ring
  · simp only [star_mul,hstar]
    ring

/-- The whole correction is itself the same literal frozen block with
a real joint multiplier inserted into K. This retains both orientations. -/
theorem source_original_unfiltered_ideal_TILT_ERROR_AS_K434
    (mu r : (g : G) → BP g → ℝ) (V : G → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : Active → ℂ) :
    sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m patterns
      mu r V K dsmall zeta theta o k F H =
    ∑ s : Active,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      star ((sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)*
      sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V
        (sourceOriginalUnfilteredIdealTiltCorrectionK434 BP J ell m patterns r K)
          dsmall zeta theta o k
          (fun t => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ)*H t) s := by
  unfold sourceOriginalUnfilteredIdealFrozenTiltError434 sourceOriginalB26FrozenBigBlock434
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  unfold sourceOriginalB26FrozenBigWeight434
  dsimp only [sourceOriginalUnfilteredIdealTiltCorrectionK434]
  have he :
      sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m (patterns h.1) r
        (fun g i => s g (h.2.2.1 g i)) (fun g i => t g (h.2.2.2 g i))
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) =
      sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m (patterns h.1) r
        s t h.2.2.1 h.2.2.2 := rfl
  rw [he,← Complex.ofReal_one,← Complex.ofReal_sub,
    source_original_unfiltered_ideal_REAL_EDGE_SCALAR434]
  split_ifs <;> ring

/-- Quantitative common-density perturbation for the ACTUAL signed frozen
family. Only the perturbation pays the absolute family cap. The main
harmonic term remains the fully cancelled family from the primary theorem. -/
theorem source_original_unfiltered_ideal_TILT_ERROR_BOUND434
    (hmJ : m ≤ J)
    (hshape : ∀ nu, ∃ p : SourceOriginalProbePattern434 G m,
      patterns nu = sourceOriginalProbeMemoryPattern434 J m hmJ p)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hnorm : ∀ g,∑ p : BP g,mu g p=1)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hVeq : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (r : (g : G) → BP g → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hr1 : ∀ g p,1 ≤ r g p) (hrR : ∀ g p,r g p ≤ R)
    (K : SourcePatternK BP J ell m patterns)
    (C : Nu → ℝ) (hC : ∀ nu,0 ≤ C nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ C nu)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : Active → ℂ) :
    ‖sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m patterns
      mu r V K dsmall zeta theta o k F H‖^2 ≤
    ((R^(2*((J+ell)*Fintype.card G))-1)*(∑ nu,C nu))^2*
      sourceOriginalB26ActiveEnergy434 BP J ell (fun g p => mu g p*(r g p)^2) F*
      sourceOriginalB26ActiveEnergy434 BP J ell (fun g p => mu g p*(r g p)^2) H := by
  let delta := R^(2*((J+ell)*Fintype.card G))-1
  have hd : 0 ≤ delta := sub_nonneg.mpr (one_le_pow₀ hR)
  have hcap (nu : Nu) (aux : SourceBigAux BP J m (patterns nu)) (s t : Active) :
      ‖sourceOriginalUnfilteredIdealTiltCorrectionK434 BP J ell m patterns r K nu aux s t‖ ≤
        delta*C nu := by
    unfold sourceOriginalUnfilteredIdealTiltCorrectionK434
    rw [norm_mul]
    exact mul_le_mul
      (source_original_unfiltered_ideal_FREE_RATIO_DEFECT434 BP J ell m (patterns nu)
        r R hR hr1 hrR s t (fun _ => Equiv.refl _) (fun _ => Equiv.refl _))
      (hK nu aux s t) (norm_nonneg _) hd
  rw [source_original_unfiltered_ideal_TILT_ERROR_AS_K434]
  have hb := source_original_unfiltered_ideal_FROZEN_ABSOLUTE_CAP434
    BP bm J ell m hmJ patterns hshape mu hmu hnorm V hV hVeq
    (sourceOriginalUnfilteredIdealTiltCorrectionK434 BP J ell m patterns r K)
    (fun nu => delta*C nu) (fun nu => mul_nonneg hd (hC nu)) hcap
    dsmall zeta theta o k
    (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)
    (fun t => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ)*H t)
  have he (f : Active → ℂ) :
      sourceOriginalB26ActiveEnergy434 BP J ell mu
        (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*f s) =
      sourceOriginalB26ActiveEnergy434 BP J ell (fun g p => mu g p*(r g p)^2) f := by
    unfold sourceOriginalB26ActiveEnergy434 sourceOriginalUnfilteredIdealCommonDensity434
    apply Finset.sum_congr rfl
    intro s _
    rw [norm_mul,mul_pow,Complex.sq_norm]
    simp only [Complex.normSq_ofReal,Finset.prod_mul_distrib,Finset.prod_pow]
    ring
  rw [he F,he H,← Finset.mul_sum] at hb
  exact hb

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealCanonicalTilt -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The common-density perturbation bound instantiated with the ORIGINAL
full RAW-none plus canonical comparison K, oriented FIRST and then filtered
by the true target birth-list Nodup. Every pointwise cap and every shape
condition is discharged. This bounds the tilt ERROR, not the full physical
CLEAN norm: the harmonic target-collision error is still a separate debt. -/
theorem source_original_unfiltered_ideal_CANONICAL_PHYSICAL_TILT_ERROR434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hVeq : ∀ g,∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ)=V g)
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
    (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
    (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
    (hxi : 0 < xi)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (pmin : ℝ) (hpmin : 0 < pmin)
    (hPrime : ∀ g (p : {p : ℕ // p ∈ P g}),pmin ≤ (p.val:ℝ))
    (hVisits : (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) < pmin)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP bm V
    let r := sourceOriginalB26PhysicalTiltRoot434 BP bm q N
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K0 := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
    let K := sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m pats
      (memoryOrientationK BP J ell m pats K0 o)
    let R := Real.sqrt ((1-(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/pmin)⁻¹)
    let C := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
    ‖sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m pats mu r V K
      dsmall zeta theta o k F H‖^2 ≤
    ((R^(2*((J+ell)*Fintype.card G))-1)*
      (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,C nu))^2*
      sourceOriginalB26ActiveEnergy434 BP J ell (physicalSourceMuTilde BP bm q N V) F*
      sourceOriginalB26ActiveEnergy434 BP J ell (physicalSourceMuTilde BP bm q N V) H := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP bm V
  let r := sourceOriginalB26PhysicalTiltRoot434 BP bm q N
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K0 := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
  let K := sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m pats
    (memoryOrientationK BP J ell m pats K0 o)
  let R := Real.sqrt ((1-(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/pmin)⁻¹)
  let C := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  obtain ⟨ha,hR,hr⟩ := source_original_unfiltered_ideal_PHYSICAL_ROOT_RANGE434
    BP bm q hq hq1 N pmin hpmin hPrime hVisits
  obtain ⟨hmu,hnorm⟩ := source_original_joint_harmonic_normalized434
    BP bm V hV (fun g => (hVeq g).symm)
  have hshape (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m) :
      ∃ p : SourceOriginalProbePattern434 G m,
        pats nu = sourceOriginalProbeMemoryPattern434 J m hmJ p := by
    cases nu with
    | none =>
      exact ⟨(∅,∅),(source_original_unfiltered_ideal_empty_pattern434.{0} J m hmJ).symm⟩
    | some nu => exact ⟨nu.val,rfl⟩
  have hC (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m) : 0 ≤ C nu :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu
  have hKo (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m)
      (aux : SourceBigAux BP J m (pats nu)) (s t : SourceOriginalB26Active434 BP J ell) :
      ‖memoryOrientationK BP J ell m pats K0 o nu aux s t‖ ≤ C nu := by
    unfold memoryOrientationK
    split_ifs
    · exact source_original_memory_RAW_COMPARISON_K_cap434
        P V blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi nu aux s t
    · exact source_original_memory_RAW_COMPARISON_K_cap434
        P V blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi nu aux t s
  have hK (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m)
      (aux : SourceBigAux BP J m (pats nu)) (s t : SourceOriginalB26Active434 BP J ell) :
      ‖K nu aux s t‖ ≤ C nu := by
    dsimp only [K,sourceOriginalUnfilteredIdealTargetNodupK434]
    split_ifs
    · exact hKo nu aux s t
    · simpa only [norm_zero] using hC nu
  have hb := source_original_unfiltered_ideal_TILT_ERROR_BOUND434 BP bm J ell m pats
    hmJ hshape mu hmu hnorm V hV hVeq r R hR
    (fun g p => (hr g p).2.1) (fun g p => (hr g p).2.2)
    K C hC hK dsmall zeta theta o k F H
  have he : physicalSourceMuTilde BP bm q N V = (fun g p => mu g p*(r g p)^2) := by
    funext g p
    exact source_original_B26_PHYSICAL_TILT_ATOM434 BP bm q N V g p (hr g p).1
  rw [← he] at hb
  exact hb

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern G J m)
local notation "A" => SourceOriginalB26Active434 BP J ell

/-- The actual frozen pairing, abbreviated without changing its weights. -/
def sourceOriginalUnfilteredPhysicalPair434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : A → ℂ) : ℂ :=
  ∑ s,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*star (F s)*
    sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
      dsmall zeta theta o k H s

/-- Exact signed split into true target-Nodup and removed birth batches. -/
theorem source_original_physical_PAIR_NODUP_SPLIT434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : A → ℂ) :
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V K
      dsmall zeta theta o k F H =
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
      (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
      dsmall zeta theta o k F H +
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
      (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m patterns K)
      dsmall zeta theta o k F H := by
  unfold sourceOriginalUnfilteredPhysicalPair434 sourceOriginalB26FrozenBigBlock434
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  unfold sourceOriginalB26FrozenBigWeight434
  dsimp only [sourceOriginalUnfilteredIdealTargetNodupK434,
    sourceOriginalUnfilteredPhysicalBadK434]
  by_cases hn : (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
      (fun g i => t g (h.2.2.2 g i))).Nodup <;>
    simp [hn,originalEdgeScalar,originalOrientedKernel]

/-- One common A for the WHOLE signed family; the filter follows full orientation when K is oriented.
The three terms retain all frame, auxiliary, phase and endpoint information. -/
theorem source_original_physical_EXACT_THREE_TERM434
    (mu r : (g : G) → BP g → ℝ) (V : G → ℝ) (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : A → ℂ) :
    let AF := fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s
    let AH := fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*H s
    let ND := sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns (fun g p => mu g p*(r g p)^2)
      V ND dsmall zeta theta o k F H =
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V K
      dsmall zeta theta o k AF AH +
    sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m patterns
      mu r V ND dsmall zeta theta o k F H -
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
      (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m patterns K)
      dsmall zeta theta o k AF AH := by
  dsimp only
  have hc := source_original_unfiltered_ideal_FROZEN_COMMON_PAIR434 BP bm J ell m
    patterns mu r V (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
    dsmall zeta theta o k F H
  have hs := source_original_physical_PAIR_NODUP_SPLIT434 BP bm J ell m patterns mu V K
    dsmall zeta theta o k
    (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)
    (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*H s)
  change sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns
      (fun g p => mu g p*(r g p)^2) V
      (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
      dsmall zeta theta o k F H =
    sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
      (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
      dsmall zeta theta o k
      (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)
      (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*H s) +
    sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m patterns mu r V
      (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
      dsmall zeta theta o k F H at hc
  rw [hc,hs]
  abel

/-- Harmonic atom bound derived from the original positive mass and prime floors. -/
theorem source_original_physical_harmonic_atom434
    (V : G → ℝ) (vmin pmin : ℝ) (hv : 0 < vmin) (hp : 0 < pmin)
    (hV : ∀ g,vmin ≤ V g) (hP : ∀ g p,pmin ≤ (bm g p:ℝ))
    (g : G) (p : BP g) :
    sourceOriginalJointHarmonicMu434 BP bm V g p ≤ 1/(vmin*pmin) := by
  have hbp : 0 < (bm g p:ℝ) := hp.trans_le (hP g p)
  change (1/(bm g p:ℝ))/V g ≤ _
  rw [div_div]
  apply one_div_le_one_div_of_le (mul_pos hv hp)
  calc
    vmin*pmin ≤ V g*(bm g p:ℝ) :=
      mul_le_mul (hV g) (hP g p) hp.le (hv.trans_le (hV g)).le
    _ = _ := mul_comm _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalRates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Coarse geometric bound. The exponent is fixed before the asymptotic threshold. -/
theorem source_original_physical_inverse_power434
    (a : ℝ) (ha : (1:ℝ)/2 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ a⁻¹^k-1 ∧ a⁻¹^k-1 ≤ (k:ℝ)*(1-a)*2^k := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hb1 : 1 ≤ a⁻¹ := (one_le_inv₀ ha0).mpr ha1
  have hb2 : a⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha0).mpr
    linarith
  have hdiff : a⁻¹-1 ≤ 2*(1-a) := by
    have h := mul_le_mul_of_nonneg_right hb2 (sub_nonneg.mpr ha1)
    have he : a⁻¹*a=1 := inv_mul_cancel₀ ha0.ne'
    nlinarith only [h,he]
  have hnonneg (n : ℕ) : 0 ≤ a⁻¹^n-1 := sub_nonneg.mpr (one_le_pow₀ hb1)
  refine ⟨hnonneg k,?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hb0
    have hmul2 := mul_le_mul_of_nonneg_right hb2
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr ha1)) (by positivity : 0 ≤ (2:ℝ)^k))
    have hpow : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hpow
      (by linarith : 0 ≤ 2*(1-a))
    simp only [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith only [hmul,hmul2,hdiff,hlast]

theorem source_original_physical_sqrt_power434
    (a : ℝ) (ha : (1:ℝ)/2 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ (Real.sqrt a⁻¹)^(2*k)-1 ∧
      (Real.sqrt a⁻¹)^(2*k)-1 ≤ (k:ℝ)*(1-a)*2^k := by
  have ha0 : 0 ≤ a := by linarith
  rw [pow_mul,Real.sq_sqrt (inv_nonneg.mpr ha0)]
  exact source_original_physical_inverse_power434 a ha ha1 k

theorem source_original_physical_two_pow_log434
    (M n : ℕ) (C0 L : ℝ) (hL : 1 ≤ L) (hC0 : 0 ≤ C0)
    (hn : (n:ℝ) ≤ C0*Real.log L) :
    (2:ℝ)^(M*n) ≤ L^((M:ℝ)*C0*Real.log 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (Nat.cast_nonneg M) (Real.log_nonneg (by norm_num : (1:ℝ)≤2)))
  push_cast
  nlinarith only [h]

/-- Source visits have a fixed polynomial budget, including both sqrt(q) endpoints. -/
theorem source_original_physical_visit_polynomial434
    (L q : ℝ) (hL : 1 ≤ L) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ ∑ i ∈ Finset.range (2*Nat.ceil (L^(0.52:ℝ))+1),
      sourceVisitEta q (2*Nat.ceil (L^(0.52:ℝ))) i ∧
    (∑ i ∈ Finset.range (2*Nat.ceil (L^(0.52:ℝ))+1),
      sourceVisitEta q (2*Nat.ceil (L^(0.52:ℝ))) i) ≤ 5*L := by
  obtain ⟨h0,h1⟩ := source_original_B26_visit_sum_unit434 q hq hq1
    (2*Nat.ceil (L^(0.52:ℝ)))
  refine ⟨h0,h1.trans ?_⟩
  have hpow : L^(0.52:ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0.52:ℝ) ≤ 1)
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hL) (0.52:ℝ))).le
  push_cast
  linarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalEventual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Both error terms decay faster than every fixed log power. M and every polynomial
exponent are fixed before L. There is no collision or norm-saving hypothesis. -/
theorem eventually_source_original_physical_ERRORS434
    (gamma v C0 B E : ℝ) (M : ℕ) (hg : 0 < gamma) (hv : 0 < v) (hC0 : 0 ≤ C0) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ (n : ℕ) (S q : ℝ), (n:ℝ) ≤ C0*Real.log L →
        0 ≤ S → S ≤ L^B → 0 ≤ q → q ≤ 1 →
      let N := 2*Nat.ceil (L^(0.52:ℝ))
      let H := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
      let P := Real.exp (L^gamma)
      let a := 1-H/P
      let delta := (Real.sqrt a⁻¹)^(2*(M*n))-1
      (1:ℝ)/2 ≤ a ∧ H < P ∧
      S^2*((((M*n:ℕ):ℝ)^2)*(1/(v*P))) ≤ L^(-(2*E)) ∧
      (S*delta)^2 ≤ L^(-(2*E)) := by
  let K0 := (M:ℝ)*C0
  have hK0 : 0 ≤ K0 := mul_nonneg (Nat.cast_nonneg M) hC0
  filter_upwards [
    eventually_source_fixed_poly_exp_saving gamma 10 1 0 hg,
    eventually_source_fixed_poly_exp_saving gamma (K0^2/v) (2*B+2) (2*E) hg,
    eventually_source_fixed_poly_exp_saving gamma (5*K0) (B+2+K0*Real.log 2) E hg,
    eventually_ge_atTop (2:ℝ)] with L hbase hbad htilt hL2
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  refine ⟨hL2,?_⟩
  intro n S q hn hS hSB hq hq1
  dsimp only
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  let P := Real.exp (L^gamma)
  let a := 1-H/P
  let delta := (Real.sqrt a⁻¹)^(2*(M*n))-1
  change (1:ℝ)/2 ≤ a ∧ H < P ∧
    S^2*((((M*n:ℕ):ℝ)^2)*(1/(v*P))) ≤ L^(-(2*E)) ∧
    (S*delta)^2 ≤ L^(-(2*E))
  have hP : 0 < P := Real.exp_pos _
  obtain ⟨hH0,hH⟩ := source_original_physical_visit_polynomial434 L q hL hq hq1
  change 0 ≤ H at hH0
  change H ≤ 5*L at hH
  have hbase' : 10*L/P ≤ 1 := by
    simpa only [Real.rpow_one,Real.rpow_zero,div_one,Real.exp_neg,div_eq_mul_inv,P,inv_one,mul_one] using hbase.2
  have hhalf : H/P ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hP).mpr
    have hp := (div_le_iff₀ hP).mp hbase'
    nlinarith only [hp,hH]
  have ha : (1:ℝ)/2 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := sub_le_self _ (div_nonneg hH0 hP.le)
  have hHP : H < P := by
    have hp := (div_le_iff₀ hP).mp hhalf
    linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hnL : (n:ℝ) ≤ C0*L := hn.trans (mul_le_mul_of_nonneg_left hlog hC0)
  have hkL : ((M*n:ℕ):ℝ) ≤ K0*L := by
    have h := mul_le_mul_of_nonneg_left hnL (Nat.cast_nonneg M : (0:ℝ) ≤ _)
    simpa only [Nat.cast_mul,mul_assoc,K0] using h
  have hS2 := pow_le_pow_left₀ hS hSB 2
  have hk2 := pow_le_pow_left₀ (Nat.cast_nonneg (M*n) : (0:ℝ) ≤ _) hkL 2
  have hbadpoly :
      S^2*((((M*n:ℕ):ℝ)^2)*(1/(v*P))) ≤
        (K0^2/v)*L^(2*B+2)*Real.exp (-(L^gamma)) := by
    calc
      _ ≤ (L^B)^2*((K0*L)^2*(1/(v*P))) := by
        exact mul_le_mul hS2 (mul_le_mul_of_nonneg_right hk2 (by positivity))
          (by positivity) (by positivity)
      _ = _ := by
        rw [show 2*B+2=B*2+2 by ring,Real.rpow_add hLp,Real.rpow_mul hLp.le,Real.rpow_two,Real.rpow_two,Real.exp_neg]
        dsimp only [P]
        ring
  have hbadfin : S^2*((((M*n:ℕ):ℝ)^2)*(1/(v*P))) ≤ L^(-(2*E)) := by
    apply hbadpoly.trans
    simpa only [Real.rpow_neg hLp.le,one_div] using hbad.2
  obtain ⟨hd0,hd⟩ := source_original_physical_sqrt_power434 a ha ha1 (M*n)
  change 0 ≤ delta at hd0
  change delta ≤ ((M*n:ℕ):ℝ)*(1-a)*2^(M*n) at hd
  have hpow := source_original_physical_two_pow_log434 M n C0 L hL hC0 hn
  have hratio : 1-a ≤ 5*L/P := by
    dsimp only [a]
    have h := div_le_div_of_nonneg_right hH hP.le
    linarith only [h]
  have hdpoly : delta ≤ 5*K0*L^(2+K0*Real.log 2)*Real.exp (-(L^gamma)) := by
    calc
      _ ≤ ((M*n:ℕ):ℝ)*(1-a)*2^(M*n) := hd
      _ ≤ (K0*L)*(5*L/P)*L^(K0*Real.log 2) := by
        exact mul_le_mul
          (mul_le_mul hkL hratio (sub_nonneg.mpr ha1) (mul_nonneg hK0 hLp.le))
          hpow (by positivity) (by positivity)
      _ = _ := by
        rw [Real.rpow_add hLp,Real.rpow_two,Real.exp_neg]
        dsimp only [P]
        ring
  have hSd : S*delta ≤ L^(-E) := by
    calc
      _ ≤ L^B*(5*K0*L^(2+K0*Real.log 2)*Real.exp (-(L^gamma))) :=
        mul_le_mul hSB hdpoly hd0 (Real.rpow_nonneg hLp.le _)
      _ = (5*K0)*L^(B+2+K0*Real.log 2)*Real.exp (-(L^gamma)) := by
        simp only [Real.rpow_add hLp]
        ring
      _ ≤ L^(-E) := by simpa only [Real.rpow_neg hLp.le,one_div] using htilt.2
  refine ⟨ha,hHP,hbadfin,?_⟩
  have hsq := pow_le_pow_left₀ (mul_nonneg hS hd0) hSd 2
  apply hsq.trans_eq
  rw [← Real.rpow_two,← Real.rpow_mul hLp.le]
  congr 1
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalBig -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Unconditional eventual BIG bound for the actual complete signed RAW-none plus
canonical comparison family, with the true numerical target-birth Nodup after
full orientation and the original physicalSourceMuTilde. The harmonic saving,
collision estimate, common-density bridge and exponential error bounds are all
proved inputs, not new analytic hypotheses. Fixed J precedes the L threshold. -/
theorem eventually_source_original_physical_FULL_TILTED_NODUP_BIG434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi : ℕ), 1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
    ∀ (J ell : ℕ) (hmJ : m ≤ J) (hell : 1 ≤ ell),
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (hcountA : c*Real.log L ≤ (blockA.card:ℝ))
      (hcountB : c*Real.log L ≤ (blockB.card:ℝ))
      (zeta theta : ℝ) (hZeta : |zeta| ≤ L^Cfreq)
      (dsmall : ℕ) (hdsmall : 0 < dsmall)
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q (fun _ => h) (fun _ => h) xi
    ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m pats mu data.Vbig
        (sourceOriginalUnfilteredIdealTargetNodupK434 BP (fun _ p => p.val) J ell m pats
          (memoryOrientationK BP J ell m pats K o)) dsmall zeta theta o k H s)‖^2 ≤
      9*L^(-(2*E))*sourceOriginalJointBigEnergy434 BP mu F*
        sourceOriginalJointBigEnergy434 BP mu H := by
  obtain ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,hMain⟩ :=
    eventually_source_original_unfiltered_ideal_FULL_SIGNED_FROZEN434
      cfg gamma dscale E Cfreq c hgamma hd hE hc
  let B := (m:ℝ)*cfg.C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  have hcexp : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,?_⟩
  intro J ell hmJ hell
  filter_upwards [hMain J ell hmJ hell,
    eventually_source_original_physical_ERRORS434 cfg.cexp cfg.vmin cfg.C0 B E (J+ell)
      hcexp cfg.hv cfg.hC0] with L hMain hErr
  dsimp only at hMain ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hMain⟩ := hMain
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hBlocks hcountA hcountB zeta theta hZeta dsmall hdsmall o k ho hk
    q hq hq1 F H
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let pmin := Real.exp (L^cfg.cexp)
  let mu := sourceOriginalJointHarmonicMu434 BP bm data.Vbig
  let nu := physicalSourceMuTilde BP bm q N data.Vbig
  let r := sourceOriginalB26PhysicalTiltRoot434 BP bm q N
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K0 := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
    J ell m hmJ Q (fun _ => h) (fun _ => h) xi
  let K := memoryOrientationK BP J ell m pats K0 o
  let ND := sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m pats K
  let C := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  let S := ∑ i : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,C i
  let eta := 1/(cfg.vmin*pmin)
  let eps := ((((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta)
  let R := Real.sqrt ((1-(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/pmin)⁻¹)
  let delta := R^(2*((J+ell)*Fintype.card G))-1
  let AF := fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s
  let AH := fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*H s
  let EF := sourceOriginalB26ActiveEnergy434 BP J ell nu F
  let EH := sourceOriginalB26ActiveEnergy434 BP J ell nu H
  have hV (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVeq (g : G) : (∑ p : BP g,1/(bm g p:ℝ))=data.Vbig g := by
    change (∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ))=data.Vbig g
    exact (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
  obtain ⟨hmu,hnorm⟩ := source_original_joint_harmonic_normalized434
    BP bm data.Vbig hV (fun g => (hVeq g).symm)
  have hC (i : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m) : 0 ≤ C i :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hC i)
  have hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hc : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hc : ((blockA.card+blockB.card:ℕ):ℝ) ≤ (Fintype.card G:ℝ)).trans data.hBigGroups
  have hSB : S ≤ L^B := source_original_memory_RAW_COMPARISON_cap_budget434
    blockA blockB m Q L cfg.C0 xi Cq Cxi hErr.1 cfg.hC0 hxi hGroups hQcap hxicap
  have hBudget := hErr.2 (Fintype.card G) S q data.hBigGroups hS hSB hq hq1
  change (1:ℝ)/2 ≤ 1-(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/pmin ∧
    (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) < pmin ∧
    S^2*eps ≤ L^(-(2*E)) ∧ (S*delta)^2 ≤ L^(-(2*E)) at hBudget
  have hPrime (g : G) (p : BP g) : pmin ≤ (bm g p:ℝ) := hTbLower g p.val p.property
  have hpmin : 0 < pmin := Real.exp_pos _
  obtain ⟨ha,hR,hr⟩ := source_original_unfiltered_ideal_PHYSICAL_ROOT_RANGE434
    BP bm q hq hq1 N pmin hpmin hPrime hBudget.2.1
  have hnu : nu = (fun g p => mu g p*(r g p)^2) := by
    funext g p
    exact source_original_B26_PHYSICAL_TILT_ATOM434 BP bm q N data.Vbig g p (hr g p).1
  have hnupos (g : G) (p : BP g) : 0 < nu g p := by
    rw [hnu]
    have hmp : 0 < mu g p := div_pos
      (one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos (bm g p)))) (hV g)
    exact mul_pos hmp (sq_pos_of_pos (zero_lt_one.trans_le (hr g p).2.1))
  have hEF : 0 ≤ EF := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (hnupos g _).le)))
      (sq_nonneg _))
  have hEH : 0 ≤ EH := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (hnupos g _).le)))
      (sq_nonneg _))
  have hEnergy (f : SourceOriginalB26Active434 BP J ell → ℂ) :
      sourceOriginalB26ActiveEnergy434 BP J ell mu
        (fun s => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*f s) =
      sourceOriginalB26ActiveEnergy434 BP J ell nu f := by
    rw [hnu]
    unfold sourceOriginalB26ActiveEnergy434 sourceOriginalUnfilteredIdealCommonDensity434
    apply Finset.sum_congr rfl
    intro s _
    rw [norm_mul,mul_pow,Complex.sq_norm]
    simp only [Complex.normSq_ofReal,Finset.prod_mul_distrib,Finset.prod_pow]
    ring
  have hKo (i : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m)
      (aux : SourceBigAux BP J m (pats i)) (s t : SourceOriginalB26Active434 BP J ell) :
      ‖K i aux s t‖ ≤ C i := by
    dsimp only [K,memoryOrientationK]
    split_ifs
    · exact source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi i aux s t
    · exact source_original_memory_RAW_COMPARISON_K_cap434 data.Tb data.Vbig blockA blockB
        J ell m hmJ Q (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi i aux t s
  have hAtom (g : G) (p : BP g) : mu g p ≤ eta :=
    source_original_physical_harmonic_atom434 BP bm data.Vbig cfg.vmin pmin cfg.hv hpmin data.hVbig hPrime g p
  have hb := source_original_physical_FROZEN_BAD_FAMILY434 BP bm J ell m
    (fun _ => Subtype.val_injective) pats mu hmu hnorm eta (one_div_nonneg.mpr (mul_pos cfg.hv hpmin).le) hAtom
    data.Vbig hV hVeq K C hC hKo dsmall zeta theta o k AF AH
  change ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats mu data.Vbig
    (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m pats K) dsmall zeta theta o k AF AH‖^2 ≤
    S^2*eps*sourceOriginalB26ActiveEnergy434 BP J ell mu AF*
      sourceOriginalB26ActiveEnergy434 BP J ell mu AH at hb
  dsimp only [AF,AH] at hb
  rw [hEnergy F,hEnergy H] at hb
  have ht := source_original_unfiltered_ideal_CANONICAL_PHYSICAL_TILT_ERROR434
    data.Tb data.Vbig hV hVeq blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi
    (fun _ _ => hh) (fun _ _ => hh) hxi q hq hq1 N pmin hpmin hPrime hBudget.2.1
    dsmall zeta theta o k F H
  change ‖sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m pats mu r data.Vbig ND
      dsmall zeta theta o k F H‖^2 ≤ (delta*S)^2*EF*EH at ht
  have hm0 := hMain x Y Hprime data sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge
    hTbLower hVbig blockA blockB hBlocks hcountA hcountB zeta theta hZeta dsmall hdsmall o k ho hk AF AH
  have hm1 : ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats mu data.Vbig K
      dsmall zeta theta o k AF AH‖^2 ≤ L^(-(2*E))*EF*EH := by
    have he := hm0
    simp only [sourceOriginalJointBigEnergy434,sourceOriginalJointBigMass434,
      sourceOriginalRealBigProductMass434,Complex.normSq_eq_norm_sq] at he
    change ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats mu data.Vbig K
      dsmall zeta theta o k AF AH‖^2 ≤ L^(-(2*E))*
      sourceOriginalB26ActiveEnergy434 BP J ell mu AF*sourceOriginalB26ActiveEnergy434 BP J ell mu AH at he
    dsimp only [AF,AH] at he
    rw [hEnergy F,hEnergy H] at he
    exact he
  have heq := source_original_physical_EXACT_THREE_TERM434 BP bm J ell m pats mu r
    data.Vbig K dsmall zeta theta o k F H
  dsimp only at heq
  rw [← hnu] at heq
  have hthree := source_original_unfiltered_ideal_three_square434
    (sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats mu data.Vbig K dsmall zeta theta o k AF AH)
    (sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m pats mu r data.Vbig ND dsmall zeta theta o k F H)
    (sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats mu data.Vbig
      (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m pats K) dsmall zeta theta o k AF AH)
  simp only [sourceOriginalJointBigEnergy434,sourceOriginalJointBigMass434,
    sourceOriginalRealBigProductMass434,Complex.normSq_eq_norm_sq]
  change ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m pats nu data.Vbig ND
    dsmall zeta theta o k F H‖^2 ≤ 9*L^(-(2*E))*EF*EH
  rw [heq]
  have hbfin := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBudget.2.2.1 hEF) hEH
  have htfin := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBudget.2.2.2 hEF) hEH
  rw [mul_comm delta S] at ht
  nlinarith only [hthree,hm1,hb,ht,hbfin,htfin]
end Green64Analytic.CorrelationSquare

end

end

