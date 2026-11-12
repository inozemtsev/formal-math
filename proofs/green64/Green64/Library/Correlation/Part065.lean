module

public import Green64.Library.Correlation.Part064
public import Green64.Library.Correlation.Part062
public import Green64.Library.Weights.Part090
public import Green64.Library.Analysis.Estimates.Part013
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part094
public import Green64.Library.Correlation.Part063
public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.Part070
public import Green64.Library.Weights.Part020
public import Green64.Library.Analysis.Estimates.Part011
public import Mathlib
public import Green64.Library.Weights.Part086
public import Green64.Library.Correlation.Part058

@[expose] public section

/-!
# Correlation / Part065

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGlobalRootHigh -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Actual coherent high-rank bound, with all source suffix and tilt laws discharged.
The whole initial vacuum mass occurs exactly once; the signed term is literal. -/
theorem eventually_source_original_global_root_SOURCE_HIGH434
    (c vmin q rho W w : ℝ) (hc : 0 < c) (hv : 0 < vmin)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hW : 1 ≤ W) (hw : 1 ≤ w)
    (hcontrol : 1/(rho*w)+Real.sqrt q/rho^2 ≤ 1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p∈P g}),NeZero p.val]
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g) (hVW : ∀ g,V g ≤ W)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ)=V g)
      (hBig : ∀ g (p : {p : ℕ // p∈P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (conductor : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
      (hhA : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (cap : G → ℕ),
    let BP := fun g => {p : ℕ // p∈P g}
    let bm := fun (g : G) (p : BP g) => p.val
    let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
    let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
    let delta := 2/(vmin*Real.exp (L^c))
    let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi

    ∀ {A : ℕ} (p : SourceOriginalRootForest434 A)
      (hSize : A=(2*Nat.ceil (L^(0.52:ℝ))+1)*Fintype.card G*(J+ell+Nat.ceil (L^2)))
      (zeta theta : ℝ) (k : ℤ),
    ‖sourceOriginalRootFunctionalRoot434 SP sm BP bm J ell m cap pat
      q rho Vs V K zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))
      (sourceOriginalRootListForestTerm434 p)‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*Nat.ceil (L^(0.52:ℝ))):ℂ)‖ *
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
        (physicalVacuum SP sm BP bm J ell) *
      (Real.exp (4*W*w*(Fintype.card G:ℝ)/rho))^(2*Nat.ceil (L^(0.52:ℝ))+1)*
      a^(2*Nat.ceil (L^(0.52:ℝ)))*delta^(sourceOriginalRootForestRank434 p) := by
  filter_upwards [eventually_source_original_root_SOURCE_RANK_SUFFIX434
    c vmin q rho W w hc hv hq hq1 hr hr1 hW hw hcontrol,
    eventually_source_original_forest_TILT_LAWS434 c vmin q hc hv hq.le hq1.le]
    with L hRank hTilt
  intro SG instSG instDSG SP instSP instDSP sm instSM G instG instDG P instP
    V hV hVW hHarmonic hBig Vs hVs blockA blockB J ell m hmJ conductor hA hB xi hhA hhB hxi cap
  dsimp only
  intro A p hSize zeta theta k
  let BP := fun g => {p : ℕ // p∈P g}
  let bm := fun (g : G) (p : BP g) => p.val
  let pat := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ conductor hA hB xi
  let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
  let delta := 2/(vmin*Real.exp (L^c))
  let a := sourceOriginalRootPinnedRowBudget434 Vs V blockA blockB ell m conductor q rho w xi
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let Gamma := Real.exp (4*W*w*(Fintype.card G:ℝ)/rho)
  let B := delta^(sourceOriginalRootForestRank434 p)*Gamma^(N+1)*a^N
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP bm V (fun g => Subtype.val_injective) hV hHarmonic hBig
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have ha : 0 ≤ a := source_original_root_PINNED_ROW_BUDGET_NONNEG434
    Vs V blockA blockB ell m conductor q rho w xi hVs hq1.le hr1.le hw0.le
  have hd : 0 ≤ delta := by dsimp [delta]; positivity
  have hBudget : 0 ≤ B := by dsimp [B,Gamma]; positivity
  have hb := source_original_global_root_CONSTRAINT_BOUNDARY434 SP sm BP bm J ell m cap pat
    q rho (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2)) Vs V hVs hmu K zeta theta k p hSize B w hBudget
  have hbound : ∀ y : FullPhysicalOutput SP sm BP bm (J+ell),
      (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup →
      ‖sourceOriginalRootForestPrefix434 p
          ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)*
        sourceOriginalRootConstraintChain434 SP sm BP bm J ell m cap pat p
          q rho Vs V mu K zeta theta k N (Nat.ceil (L^2))
          (fun out _ => physicalVacuum SP sm BP bm J ell out) N 0 y
          ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)‖ ≤
      B*w^(∑ g,(y.2 g).2.card) := by
    intro y hn
    apply hRank SP sm P V hV hVW hHarmonic hBig Vs hVs blockA blockB J ell m hmJ
      conductor hA hB xi hhA hhB hxi cap p zeta theta k N 0 y
      ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)
    · rw [source_original_root_INITIAL_PAD_LENGTH434]
      exact hSize.trans (by dsimp only [N]; ring)
    · simpa using hn
  have hh := hb hbound
  convert hh using 1 <;> dsimp only [B,Gamma,N,a,delta,mu,K,pat,BP,bm] <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootVacuumLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem source_original_root_BOUNDARY_LOG_ALGEBRA434
    (L R C : ℝ) (M s n : ℕ) (hL : 0<L) (hlog : 1≤Real.log L)
    (hR : 1≤R) (hC : 0≤C)
    (hs : (s:ℝ)≤C*Real.log L) (hn : (n:ℝ)≤C*Real.log L) :
    (2*R*L)^(M*s)*(2:ℝ)^(M*n) ≤
      Real.exp (2*(M:ℝ)*C*(1+Real.log (2*R))*(Real.log L)^2) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have h2R : 0<2*R := by positivity
  have hbase : 0<2*R*L := by positivity
  have ha : 0≤Real.log (2*R) := Real.log_nonneg (by linarith)
  have ht : 0≤Real.log L := zero_le_one.trans hlog
  have hlog2 : Real.log 2≤Real.log (2*R) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [←Real.rpow_natCast,←Real.rpow_natCast,
    Real.rpow_def_of_pos hbase,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    ←Real.exp_add,Real.log_mul (ne_of_gt h2R) (ne_of_gt hL)]
  apply Real.exp_le_exp.mpr
  simp only [Nat.cast_mul]
  have hsa : (M:ℝ)*(s:ℝ)*(Real.log (2*R)+Real.log L) ≤
      (M:ℝ)*(C*Real.log L)*(Real.log (2*R)+Real.log L) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg M)) (add_nonneg ha ht)
  have hna : (M:ℝ)*(n:ℝ)*Real.log 2 ≤
      (M:ℝ)*(C*Real.log L)*Real.log (2*R) := by
    calc
      _ ≤ (M:ℝ)*(n:ℝ)*Real.log (2*R) :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg M)) ha
  have hnon : 0 ≤ (M:ℝ)*C*Real.log L*Real.log (2*R)*(Real.log L-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg M) hC) ht) ha)
      (sub_nonneg.mpr hlog)
  have hnon' : 0 ≤ (M:ℝ)*C*(Real.log L)^2 := by positivity
  nlinarith

/-- A finite physical vacuum bound from only the original SMALL lower
masses, upper moduli and logarithmic group counts; no Haar normalization
or BIG active-tuple injectivity is added. -/
theorem source_original_root_VACUUM_LOG_BOUND434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (P : SG → Finset ℕ) [∀ g (p : {p : ℕ // p∈P g}),NeZero p.val]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell : ℕ) (cap : BG → ℕ)
    (L b vmin C : ℝ) (hL : 1≤L) (hlog : 1≤Real.log L)
    (hb : b≤1) (hv : 0<vmin) (hC : 0≤C)
    (hsmall : (Fintype.card SG:ℝ)≤C*Real.log L)
    (hbig : (Fintype.card BG:ℝ)≤C*Real.log L)
    (hprime : ∀ g p,p∈P g → 0<p)
    (hupper : ∀ g p,p∈P g → (p:ℝ)≤Real.exp (L^b))
    (Vs : SG → ℝ) (hVs : ∀ g,vmin≤Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,(∑ p : BP g,mu g p)≤2) :
    sourceOriginalUnfilteredIdealOrbitEnergy434
      (fun g : SG => {p : ℕ // p∈P g}) (fun _ p => p.val)
      BP bm J ell cap Vs mu
      (physicalVacuum (fun g : SG => {p : ℕ // p∈P g}) (fun _ p => p.val) BP bm J ell) ≤
      Real.exp (2*((J+ell:ℕ):ℝ)*C*(1+Real.log (2*max 1 vmin⁻¹))*(Real.log L)^2) := by
  let R := max 1 vmin⁻¹
  have hRp : 0<R := zero_lt_one.trans_le (le_max_left _ _)
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hfinite := source_original_root_VACUUM_FINITE_BOUND434
    (fun g : SG => {p : ℕ // p∈P g}) (fun _ p => p.val) BP bm J ell cap
    Vs (fun g => hv.trans_le (hVs g)) mu hmu hMass
  have hH (g : SG) : (∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ))≤2*L := by
    rw [Finset.sum_coe_sort (P g) (fun p : ℕ => 1/(p:ℝ))]
    exact source_original_root_SMALL_HARMONIC_LINEAR434 (P g) L b hL hb
      (hprime g) (hupper g)
  have hratio (g : SG) : ((∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ))/Vs g)≤2*R*L := by
    have hV0 : 0<Vs g := hv.trans_le (hVs g)
    have hinv0 : (Vs g)⁻¹≤vmin⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hv (hVs g)
    have hinv : (Vs g)⁻¹≤R := hinv0.trans (le_max_right _ _)
    rw [div_eq_mul_inv]
    calc
      _ ≤ (2*L)*R := mul_le_mul (hH g) hinv (inv_nonneg.mpr hV0.le) (by positivity)
      _ = _ := by ring
  have hprod :
      (∏ g : SG,((∑ p : {p : ℕ // p∈P g},1/(p.val:ℝ))/Vs g)^(J+ell)) ≤
        (2*R*L)^((J+ell)*Fintype.card SG) := by
    calc
      _ ≤ ∏ _g : SG,(2*R*L)^(J+ell) := by
        apply Finset.prod_le_prod₀
        · intro g hg
          exact pow_nonneg (div_nonneg (Finset.sum_nonneg (fun p hp => by positivity))
            (hv.trans_le (hVs g)).le) _
        · intro g hg
          exact pow_le_pow_left₀
            (div_nonneg (Finset.sum_nonneg (fun p hp => by positivity)) (hv.trans_le (hVs g)).le)
            (hratio g) _
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←pow_mul]
  calc
    _ ≤ _ := hfinite
    _ ≤ (2*R*L)^((J+ell)*Fintype.card SG)*(2:ℝ)^((J+ell)*Fintype.card BG) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ ≤ _ := source_original_root_BOUNDARY_LOG_ALGEBRA434 L R C (J+ell)
      (Fintype.card SG) (Fintype.card BG) hL0 hlog (le_max_left _ _) hC hsmall hbig
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourceVacuum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Actual original-source coherent vacuum budget. The SMALL normalizers
are kept as supplied by the source and the BIG mass is the moving-depth
tilt. No boundary, collision or root-saving hypothesis is assumed. -/
theorem eventually_source_original_root_SOURCE_VACUUM434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p∈data.Tb g}),NeZero p.val]
      (hSmallUpper : ∀ g : Option ι,∀ p∈sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ)≤Real.exp (L^cfg.bexp))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p∈data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hBig : ∀ g,∀ p∈data.Tb g,Real.exp (L^cfg.cexp)≤(p:ℝ))
      (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p∈data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs mu (physicalVacuum SP (fun _ p => p.val) BP (fun _ p => p.val) J ell) ≤
      Real.exp (2*((J+ell:ℕ):ℝ)*(cfg.C0+1)*
        (1+Real.log (2*max 1 cfg.vmin⁻¹))*(Real.log L)^2) := by
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_forest_TILT_LAWS434
    cfg.cexp cfg.vmin cfg.q0 hc cfg.hv cfg.hq0.le cfg.hq1.le,
    eventually_ge_atTop (Real.exp 1)] with L hTilt hL
  intro ι G instI instDI instG instDG x Y Hprime data instNZ hSmallUpper hHarmonic hBig cap
  let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p∈data.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
    (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hL1 : 1≤L :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)).trans hL
  have hlog : 1≤Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using hh
  have hsmall : (Fintype.card (Option ι):ℝ)≤(cfg.C0+1)*Real.log L := by
    simp only [Fintype.card_option,Nat.cast_add,Nat.cast_one]
    nlinarith [data.hSmallGroups]
  have hbig : (Fintype.card G:ℝ)≤(cfg.C0+1)*Real.log L := by
    nlinarith [data.hBigGroups]
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP (fun _ p => p.val) data.Vbig
    (fun g => Subtype.val_injective) data.hVbig hHarmonic
    (fun g p => hBig g p.val p.property)
  exact source_original_root_VACUUM_LOG_BOUND434
    (sourceOriginalActualSmallPrimeSets434 data) BP (fun _ p => p.val)
    J ell cap L cfg.bexp cfg.vmin (cfg.C0+1) hL1 hlog cfg.hb.le cfg.hv
    (by linarith [cfg.hC0]) hsmall hbig
    (fun g p hp => ((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p hp).pos)
    hSmallUpper Vs
    (fun g => (source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
    mu (fun g p => (hmu g p).le) hmass
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootVacuumSubpower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Every fixed log-squared vacuum cost is subpower per ORIGINAL moving
visit count. The late constant C affects only the eventual threshold. -/
theorem eventually_source_original_root_LOG_SQUARED_SUBPOWER434
    (C eps : ℝ) (hC : 0≤C) (heps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C*(Real.log L)^2) ≤
        L^(eps*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) := by
  have hpow : ∀ᶠ L : ℝ in atTop,2*C/eps≤L^(0.27:ℝ) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop (by norm_num : (0:ℝ)<0.27))) (2*C/eps)
  filter_upwards [hpow,eventually_ge_atTop (1:ℝ)] with L hlarge hL
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hl : 0≤Real.log L := Real.log_nonneg hL
  have hlog : Real.log L≤4*L^(0.25:ℝ) := by
    have hh := Real.log_le_rpow_div hLp.le (by norm_num : (0:ℝ)<0.25)
    convert hh using 1 <;> ring
  have hcap : 2*C≤eps*L^(0.27:ℝ) := by
    have hh := (div_le_iff₀ heps).mp hlarge
    linarith
  have hproduct : L^(0.25:ℝ)*L^(0.27:ℝ)=L^(0.52:ℝ) := by
    rw [←Real.rpow_add hLp]
    norm_num
  have hCLog : C*Real.log L≤2*eps*L^(0.52:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg hLp.le (0.25:ℝ))
    have hl' := mul_le_mul_of_nonneg_left hlog hC
    have hh' : 4*C*L^(0.25:ℝ) ≤ 2*eps*(L^(0.25:ℝ)*L^(0.27:ℝ)) := by
      nlinarith
    rw [hproduct] at hh'
    nlinarith [hl',hh']
  have hceil : L^(0.52:ℝ)≤(Nat.ceil (L^(0.52:ℝ)):ℝ) := Nat.le_ceil _
  have hN : C*Real.log L≤eps*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    nlinarith
  rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hN hl
  nlinarith
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPotentialCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact ORIGINAL potential-address count at N=2ceil(L^.52), T=ceil(L²).
The fixed slot width precedes the threshold; the group count may move. -/
theorem eventually_source_original_root_POTENTIAL_COUNT434
    (C : ℝ) (hC : 0 ≤ C) (M : ℕ) :
    ∀ᶠ L : ℝ in atTop,∀ n : ℕ,(n:ℝ) ≤ C*Real.log L →
      (((2*Nat.ceil (L^(0.52:ℝ))+1)*n*(M+Nat.ceil (L^2)):ℕ):ℝ) ≤ L^4 := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (20*C*((M:ℝ)+2))] with L hL hlarge
  intro n hn
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hlog : Real.log L ≤ 4*L^(0.25:ℝ) := by
    have h := Real.log_le_rpow_div hLp.le (by norm_num : (0:ℝ)<0.25)
    convert h using 1 <;> ring
  have hn' : (n:ℝ) ≤ 4*C*L^(0.25:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog hC
    nlinarith
  have hN : ((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) ≤ 5*L^(0.75:ℝ) := by
    have hh := (Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (0.52:ℝ))).le
    have hpow := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0.52:ℝ)≤0.75)
    have h1 := Real.one_le_rpow hL (by norm_num : (0:ℝ)≤0.75)
    push_cast
    linarith
  have hT : (Nat.ceil (L^2):ℝ) ≤ 2*L^2 := by
    have hh := (Nat.ceil_lt_add_one (sq_nonneg L)).le
    linarith
  have hM : (M:ℝ)+(Nat.ceil (L^2):ℝ) ≤ ((M:ℝ)+2)*L^2 := by
    have hh := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg M : (0:ℝ)≤M)
    nlinarith
  have hprod : L^(0.75:ℝ)*L^(0.25:ℝ)=L := by
    rw [←Real.rpow_add hLp]
    norm_num
  calc
    _ = ((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)*(n:ℝ)*((M:ℝ)+(Nat.ceil (L^2):ℝ)) := by
      push_cast
      rfl
    _ ≤ (5*L^(0.75:ℝ))*(4*C*L^(0.25:ℝ))*(((M:ℝ)+2)*L^2) := by
      apply mul_le_mul
      · exact mul_le_mul hN hn' (Nat.cast_nonneg _) (by positivity)
      · exact hM
      · positivity
      · positivity
    _ = 20*C*((M:ℝ)+2)*L^3 := by
      calc
        _ = 20*C*((M:ℝ)+2)*(L^(0.75:ℝ)*L^(0.25:ℝ))*L^2 := by ring
        _ = _ := by rw [hprod]; ring
    _ ≤ L*L^3 := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = L^4 := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourceSubpower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem eventually_source_original_root_SOURCE_VACUUM_SUBPOWER434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p∈data.Tb g}),NeZero p.val]
      (hSmallUpper : ∀ g : Option ι,∀ p∈sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ)≤Real.exp (L^cfg.bexp))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p∈data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hBig : ∀ g,∀ p∈data.Tb g,Real.exp (L^cfg.cexp)≤(p:ℝ))
      (cap : G → ℕ),
    let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p∈data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs mu (physicalVacuum SP (fun _ p => p.val) BP (fun _ p => p.val) J ell) ≤
      L^(eps*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) := by
  let C : ℝ := 2*((J+ell:ℕ):ℝ)*(cfg.C0+1)*(1+Real.log (2*max 1 cfg.vmin⁻¹))
  have hlog : 0 ≤ Real.log (2*max 1 cfg.vmin⁻¹) := by
    apply Real.log_nonneg
    linarith [le_max_left (1:ℝ) cfg.vmin⁻¹]
  have hc0 := cfg.hC0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_source_original_root_SOURCE_VACUUM434 cfg J ell,
    eventually_source_original_root_LOG_SQUARED_SUBPOWER434 C eps hC heps] with L hv hs
  intro ι G instI instDI instG instDG x Y Hprime data instNZ hSmallUpper hHarmonic hBig cap
  exact (hv x Y Hprime data hSmallUpper hHarmonic hBig cap).trans hs
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeNearContraction -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- Actual FULL small-norm bound at common source parameters. Certified
CLEAN is reused with precision E+1; m and precisions precede the fixed J
chosen for DIRTY. No analytic CLEAN or DIRTY premise is assumed. This
local theorem still erases global seen disjointness; it is not Memory. -/
theorem eventually_source_original_edge_FULL_NEAR_CONTRACTION434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr : 0 < rho) (hr1 : rho < 1) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ)
      (F : FullPhysicalOutput
        (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g})
        (fun _ p => p.val) (fun g : G => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) (J+1) → ℂ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F) ≤
    L^(-(2*E))*sourceOriginalUnfilteredIdealOrbitEnergy434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu F := by
  have hE1 : 0 < E+1 := by linarith
  obtain ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,hClean⟩ :=
    eventually_source_original_physical_FULL_SEEN_ERASED_CLEAN434 cfg gamma dscale (E+1) Cfreq c
      hgamma hd hE1 hc
  obtain ⟨J,hmJ,hJ⟩ := source_original_edge_CHOOSE_J434 m (E+1)
    (sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin (cfg.C0+1)
      (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)) c0 hc0
  have hcexp : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hClean J hmJ,eventually_source_original_edge_SOURCE_BOUNDS434
    cfg m Cq Cxi rho vmax c0 (E+1) Ck hr hr1 hvmax hc0 hE1 J hmJ hJ,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hcexp,
    eventually_ge_atTop (3:ℝ)] with L hClean hSource hVisit hL
  dsimp only at hClean ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hClean⟩ := hClean
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta o k ho hk hkCap cap F
  let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let EC := sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J 1 m cap pats
    cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F
  let ED := sourceOriginalUnfilteredEvolutionSeenErasedDirty434 SP sm BP bm J 1 m cap pats
    cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F
  let EF := sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J 1 m cap pats
    cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F
  let En := sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J 1 cap Vs mu
  have hC : En EC ≤ L^(-(2*(E+1)))*En F :=
    hClean x Y Hprime data sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hBlocks hcountA hcountB zeta theta hZeta o k ho hk cap (Nat.ceil (L^2))
      rho hr.le hr1.le F
  have hHarmonic (g : G) : ∑ p : BP g,1/(p.val:ℝ)=data.Vbig g := by
    change (∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ))=data.Vbig g
    exact (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
  have hDirty := hSource x Y Hprime data sep hSmallUpper hTbLower hHarmonic hVmax hSmallLower
    blockA blockB hBlocks Q hQ xi hxi hQcap hxicap (fun _ => h) (fun _ => h)
    (fun _ _ => hh) (fun _ _ => hh) zeta theta o k ho hk hkCap cap F
  have hD : En ED ≤ L^(-(2*(E+1)))*En F := hDirty.2
  have hVs (g : Option ι) : 0 < Vs g := cfg.hv.trans_le
    ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hV (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*Nat.ceil (L^(0.52:ℝ))) g p (hVisit p.val (hTbLower g p.val p.property))).1
    have hb0 : 0 < physicalSourceBaseline BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) g p :=
      lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hb0)
  have hEn : 0 ≤ En F := Finset.sum_nonneg (fun X hX => mul_nonneg
    (physicalOrbitMass_pos SP sm BP bm (J+1) cap Vs mu hVs hmu X hX).le (sq_nonneg _))
  have hsum : En (fun X => EC X+ED X) ≤ 2*En EC+2*En ED :=
    source_original_edge_ENERGY_ADD434 SP sm BP bm J 1 cap Vs mu hVs hmu EC ED
  have hsplit : EF=(fun X => EC X+ED X) := by
    funext X
    exact source_original_evolution_SEEN_ERASED_FULL_SPLIT434 SP sm BP bm J 1 m cap pats
      cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F X
  have hLp : 0 < L := by linarith
  have h4 : 4*L^(-(2*(E+1))) ≤ L^(-(2*E)) := by
    have ha := source_original_physical_ABSORB_SMALL434 L E 0 1 hL (by norm_num)
      (by simp : (1:ℝ) ≤ L^(0:ℝ))
    have he : 0 ≤ L^(-(2*(E+1))) := Real.rpow_nonneg hLp.le _
    simp only [add_zero,one_pow,mul_one] at ha
    nlinarith only [ha,he]
  change En EF ≤ L^(-(2*E))*En F
  rw [hsplit]
  calc
    _ ≤ 2*En EC+2*En ED := hsum
    _ ≤ (4*L^(-(2*(E+1))))*En F := by linarith only [hC,hD]
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 hEn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourceBanks -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Joint actual source local banks at precisely the common fixed source
parameters. Saving E is chosen before m and precision; the phase exponent
is determined later and independent of J. No local norm premise is assumed. -/
theorem eventually_source_original_root_SOURCE_LOCAL_BANKS434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr : 0 < rho) (hr1 : rho < 1) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ)
      (F : FullPhysicalOutput
        (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g})
        (fun _ p => p.val) (fun g : G => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) (J+1) → ℂ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 cap Vs mu
      (sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2)) zeta theta o k F) ≤
    L^(-(2*E))*sourceOriginalUnfilteredIdealOrbitEnergy434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu F
      ∧ ∀ (phase : (st : FullPhysicalState SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) cap) →
        FullOrientedSourceChoice SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m cap pats st → ℂ)
        (hphase : ∀ st z,‖phase st z‖ ≤ 1),
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 cap Vs mu
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m cap pats (fun _ _ => True) phase cfg.q0 rho Vs data.Vbig mu K (Nat.ceil (L^2))
          zeta theta o k F) ≤
      L^(2*sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
        (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax))*
        sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 cap Vs mu F := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hNear⟩ :=
    eventually_source_original_edge_FULL_NEAR_CONTRACTION434 cfg gamma dscale E Cfreq c rho vmax c0 Ck
      hgamma hd hE hc hr hr1 hvmax hc0
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hNear,eventually_source_original_root_SOURCE_PHASE_POLY434
    cfg m Cq Cxi rho vmax c0 E Ck hr hr1 hvmax hc0 hE J hmJ] with L hNear hPoly
  dsimp only at hNear ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hNear⟩ := hNear
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta o k ho hk hkCap cap F
  constructor
  · exact hNear x Y Hprime data sep hSmallUpper hVmax hSmallLower
      loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
      zeta theta hZeta o k ho hk hkCap cap F
  · intro phase hphase
    have hHarmonic (g : G) : ∑ p : {p : ℕ // p∈data.Tb g},1/(p.val:ℝ)=data.Vbig g :=
      (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
    exact hPoly x Y Hprime data sep hSmallUpper hTbLower hHarmonic hVmax hSmallLower
      blockA blockB hBlocks (Nat.ceil (4*L^(D+1))) hQ (L^(-(Cxi:ℝ))) hxi hQcap hxicap
      (fun _ => Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ))
      (fun _ => Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ))
      (fun _ _ => hh) (fun _ _ => hh) zeta theta o k ho hk hkCap cap phase hphase F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSourceLow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Actual source forest low-rank bank. All local norms are discharged
at the common original source parameters. This is a per-forest bound,
not the missing global high-rank sum or root-decay theorem. -/
theorem eventually_source_original_root_SOURCE_FOREST_LOW434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr : 0 < rho) (hr1 : rho < 1) (hquarter : cfg.q0^(1/4:ℝ) < rho) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (k : ℤ) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ)
,
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi

    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let T := Nat.ceil (L^2)
    let A := (N+1)*Fintype.card G*(J+1+T)
    let W := max 1 vmax
    let w := max 1 (4*W/(rho*(1-Real.sqrt cfg.q0/rho^2)))
    let Gamma := Real.exp (4*W*w*(Fintype.card G:ℝ)/rho)
    let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
      (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
    ∀ p : SourceOriginalRootForest434 A,
    ‖sourceOriginalRootFunctionalRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ))) T
      (sourceOriginalRootListForestTerm434 p)‖ ≤
    ‖(physicalSourceBaselineProduct BP (fun _ p => p.val) cfg.q0 N:ℂ)‖ *
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 cap Vs mu (physicalVacuum SP (fun _ p => p.val) BP (fun _ p => p.val) J 1) *
      Gamma^(N+1)*(L^(-E))^N*(max 1 (L^kappa/L^(-E)))^(2*sourceOriginalRootForestRank434 p) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hBanks⟩ :=
    eventually_source_original_root_SOURCE_LOCAL_BANKS434 cfg gamma dscale E Cfreq c rho vmax c0 Ck
      hgamma hd hE hc hr hr1 hvmax hc0
  have hcexp : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hBanks,eventually_source_original_forest_TILT_LAWS434
    cfg.cexp cfg.vmin cfg.q0 hcexp cfg.hv cfg.hq0.le cfg.hq1.le,
    eventually_gt_atTop (0:ℝ)] with L hBanks hTilt hL
  dsimp only at hBanks ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hBanks⟩ := hBanks
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap cap
  let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p∈data.Tb g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let mu := physicalSourceMuTilde BP bm cfg.q0 N data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q
    (fun _ => h) (fun _ => h) xi
  let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
    (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
  let lo := L^(-E)
  let b := max 1 (L^kappa/lo)
  have hlo : 0 < lo := Real.rpow_pos_of_pos hL _
  have hb : 1 ≤ b := le_max_left _ _
  have hVs : ∀ g,0 < Vs g := fun g => cfg.hv.trans_le
    ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hHarmonic (g : G) : ∑ p : BP g,1/(p.val:ℝ)=data.Vbig g :=
    (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP bm data.Vbig (fun _ => Subtype.val_injective)
    data.hVbig hHarmonic (fun g p => hTbLower g p.val p.property)
  have hhi : L^kappa ≤ lo*b := by
    have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (L^kappa/lo)) hlo.le
    simpa only [mul_div_cancel₀ _ hlo.ne'] using hh
  have hsq (a : ℝ) : L^(2*a)=(L^a)^2 := by
    convert Real.rpow_mul_natCast hL.le a 2 using 1 <;> norm_num <;> ring
  have ho (i : ℕ) : physicalAlternatingSign i=1 ∨ physicalAlternatingSign i= -1 := by
    unfold physicalAlternatingSign
    split_ifs <;> simp
  have hbank (i : ℕ) (F : FullPhysicalOutput SP sm BP bm (J+1) → ℂ) :=
    hBanks x Y Hprime data sep hSmallUpper hVmax hSmallLower loB hiB hBigFull hLoLeHi
      hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
      zeta theta hZeta (physicalAlternatingSign i) k (ho i) hk hkCap cap F
  intro p
  apply source_original_root_FOREST_RANK_FINITE_BOUND434 SP sm BP bm J 1 m cap pats
    cfg.q0 rho vmax (Nat.ceil (L^(0.52:ℝ))) T _ rfl p cfg.hq0 cfg.hq1 hquarter hr1
    Vs hVs data.Vbig (fun g => (cfg.hv.trans_le (data.hVbig g)).le) hVmax
    K zeta theta k lo b hlo.le hb hmu hmass
  · intro i F
    have hh := (hbank i F).1
    have he : L^(-(2*E))=lo^2 := by
      dsimp [lo]
      convert hsq (-E) using 1 <;> ring
    simpa only [he] using hh
  · intro i phase hphase F
    have hh := (hbank i F).2 phase hphase
    have hEn : 0 ≤ sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J 1 cap Vs mu F :=
      Finset.sum_nonneg (fun X hX => mul_nonneg
        (physicalOrbitMass_pos SP sm BP bm (J+1) cap Vs mu hVs hmu X hX).le (sq_nonneg _))
    have hsqle : (L^kappa)^2 ≤ (lo*b)^2 := by
      have hnon := Real.rpow_nonneg hL.le kappa
      nlinarith
    apply hh.trans
    exact mul_le_mul_of_nonneg_right ((hsq kappa).le.trans hsqle) hEn
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootProjected -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The EXISTING original projected root, with all source banks and
rank estimates discharged at a single fixed source parameter tuple. -/
theorem eventually_source_original_global_root_PROJECTED434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr : 0 < rho) (hr1 : rho < 1) (hquarter : cfg.q0^(1/4:ℝ) < rho) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (k : ℤ) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck) (cap : G → ℕ)
,
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi

    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let T := Nat.ceil (L^2)
    let A := (N+1)*Fintype.card G*(J+1+T)
    ‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ))) T‖ ≤
    L^(-E*(N:ℝ)) := by
  let W := max 1 vmax
  let w := max 1 (4*W/(rho*(1-Real.sqrt cfg.q0/rho^2)))
  let Cv := 4*W*w*cfg.C0/rho
  have hW : 1≤W := le_max_left _ _
  have hwc := source_original_global_root_ORIGINAL_W_CONTROL434 cfg.q0 rho W cfg.hq0.le hquarter hW
  have hw : 1≤w := hwc.1
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hCv0 : 0≤Cv := by
    have hc0non := cfg.hC0
    dsimp [Cv]
    positivity
  let S := E+Cv+5
  have hS : 0<S := by dsimp [S]; linarith
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hLow⟩ :=
    eventually_source_original_root_SOURCE_FOREST_LOW434 cfg gamma dscale S Cfreq c rho vmax c0 Ck
      hgamma hd hS hc hr hr1 hquarter hvmax hc0
  let kappa := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin
    (cfg.C0+1) (sourceOriginalUnfilteredEdgeRatioBase434 cfg.vmin vmax)
  let Kr := max 0 (kappa+S)
  let Cb := sourceOriginalUnfilteredEdgeExponent434 1 m Cq Cxi cfg.q0 rho cfg.vmin (cfg.C0+1) 1+
    ((1+m:ℕ):ℝ)*(cfg.C0+1)*Real.log w
  have hcexp : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hLow,
    eventually_source_original_global_root_SOURCE_HIGH434 cfg.cexp cfg.vmin cfg.q0 rho W w
      hcexp cfg.hv cfg.hq0 cfg.hq1 hr hr1 hW hw hwc.2,
    eventually_source_original_root_SOURCE_VACUUM_SUBPOWER434 cfg J 1 1 (by norm_num),
    eventually_source_original_forest_TILT_LAWS434 cfg.cexp cfg.vmin cfg.q0
      hcexp cfg.hv cfg.hq0.le cfg.hq1.le,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hcexp,
    eventually_source_original_root_POTENTIAL_COUNT434 cfg.C0 cfg.hC0 (J+1),
    eventually_source_original_global_root_RATES434 cfg.cexp cfg.vmin E Cv Cb Kr hcexp cfg.hv,
    eventually_ge_atTop (Real.exp 1)]
    with L hLow hHigh hVac hTilt hVisits hPot hRates hExp
  dsimp only at hLow hRates ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hLow⟩ := hLow
  obtain ⟨hL,hN,hCv,hcut,hcoin,hhigh⟩ := hRates
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap cap
  let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p∈data.Tb g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let A := (N+1)*Fintype.card G*(J+1+T)
  let mu := physicalSourceMuTilde BP bm cfg.q0 N data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q
    (fun _ => h) (fun _ => h) xi
  let Gamma := Real.exp (4*W*w*(Fintype.card G:ℝ)/rho)
  let Bvac := sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J 1 cap Vs mu
    (physicalVacuum SP sm BP bm J 1)
  let beta : ℂ := (physicalSourceBaselineProduct BP bm cfg.q0 N:ℂ)
  let P0 := ‖beta‖*Bvac*Gamma^(N+1)
  let b := max 1 (L^kappa/L^(-S))
  let a := sourceOriginalRootPinnedRowBudget434 Vs data.Vbig blockA blockB 1 m Q cfg.q0 rho w xi
  let delta := 2/(cfg.vmin*Real.exp (L^cfg.cexp))
  let F : SourceOriginalRootForest434 A → ℂ := fun p =>
    sourceOriginalRootFunctionalRoot434 SP sm BP bm J 1 m cap pats cfg.q0 rho Vs data.Vbig K
      zeta theta k (Nat.ceil (L^(0.52:ℝ))) T (sourceOriginalRootListForestTerm434 p)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1≤L := le_trans (by norm_num) hL
  have hlog : 1≤Real.log L := by simpa using Real.log_le_log (Real.exp_pos 1) hExp
  have hVs : ∀ g,0<Vs g := fun g => cfg.hv.trans_le
    ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hHarmonic (g : G) : ∑ p : BP g,1/(p.val:ℝ)=data.Vbig g :=
    (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
  obtain ⟨hmu,hmass,hAtom⟩ := hTilt BP bm data.Vbig (fun _ => Subtype.val_injective)
    data.hVbig hHarmonic (fun g p => hTbLower g p.val p.property)
  have hB0 : 0≤Bvac := Finset.sum_nonneg (fun out hout => mul_nonneg
    (physicalOrbitMass_pos SP sm BP bm (J+1) cap Vs mu hVs hmu out hout).le (sq_nonneg _))
  have hP0 : 0≤P0 := by dsimp [P0,Gamma]; positivity
  have hbase (g : G) (p : BP g) : (1:ℝ)/2≤physicalSourceBaseline BP bm cfg.q0 N g p ∧
      physicalSourceBaseline BP bm cfg.q0 N g p≤1 :=
    source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le N g p
      (hVisits p.val (hTbLower g p.val p.property))
  have hbeta : ‖beta‖≤1 := source_original_ACTUAL_physical_baseline_norm_le_one434 BP bm cfg.q0 N
    (fun g p => lt_of_lt_of_le (by norm_num) (hbase g p).1) (fun g p => (hbase g p).2)
  have hBbound : Bvac≤L^(N:ℝ) := by
    simpa only [one_mul] using hVac x Y Hprime data hSmallUpper hHarmonic hTbLower cap
  have hGbound : Gamma≤L^Cv := source_original_global_root_GAMMA_POLY434 L W w rho cfg.C0
    (Fintype.card G) hLp (zero_le_one.trans hW) hw0.le hr data.hBigGroups
  have hPb : P0≤L^((Cv+2)*(N:ℝ)) := source_original_global_root_PREFACTOR434
    L Cv Bvac Gamma beta N hL1 hCv hB0 (Real.exp_pos _).le hbeta hBbound hGbound
  have hBigCount : (Fintype.card G:ℝ)≤(cfg.C0+1)*Real.log L := by
    nlinarith only [data.hBigGroups,hlog]
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ)≤(cfg.C0+1)*Real.log L := by
    have hh : blockA.card+blockB.card≤Fintype.card G := by
      rw [←Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (show (((blockA.card+blockB.card):ℕ):ℝ)≤(Fintype.card G:ℝ) by exact_mod_cast hh).trans hBigCount
  have hab : a≤L^Cb := source_original_root_PINNED_BUDGET_POLYNOMIAL434 blockA blockB 1 m Cq Cxi Q
    cfg.q0 rho cfg.vmin (cfg.C0+1) w L xi Vs data.Vbig cfg.hq0 cfg.hq1 hr hr1 cfg.hv
    (by linarith [cfg.hC0]) hw hL hxi
    (source_original_ACTUAL_SMALL_source_bounds434 data).2.2 data.hVbig
    (source_original_ACTUAL_SMALL_group_count434 data hlog) hBigCount hGroups hQcap hxicap
  have hbb : b≤L^Kr := source_original_global_root_MARKED_POLY434 L kappa S hL1
  have hb0 : 0≤b := zero_le_one.trans (le_max_left _ _)
  have ha0 : 0≤a := source_original_root_PINNED_ROW_BUDGET_NONNEG434
    Vs data.Vbig blockA blockB 1 m Q cfg.q0 rho w xi hVs cfg.hq1.le hr1.le hw0.le
  have hd0 : 0≤delta := by
    dsimp [delta]
    exact div_nonneg (by norm_num) (mul_nonneg cfg.hv.le (Real.exp_pos _).le)
  have hA : (A:ℝ)≤L^4 := hPot (Fintype.card G) data.hBigGroups
  rw [source_original_root_ORIGINAL_FOREST_SUM434]
  apply source_original_global_root_SCALAR_FOREST434 L E Cv Cb Kr cfg.cexp P0 b a delta A N
    hL hN hE.le hP0 hb0 ha0 hd0 hA (le_max_left _ _) hCv hPb hbb hab hcut
    (hcoin A hA) hhigh F
  · intro p
    exact hLow x Y Hprime data sep hSmallUpper hVmax hSmallLower loB hiB hBigFull hLoLeHi
      hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
      zeta theta hZeta k hk hkCap cap p
  · intro p
    exact hHigh SP sm data.Tb data.Vbig data.hVbig (fun g => (hVmax g).trans (le_max_right _ _))
      hHarmonic (fun g p => hTbLower g p.val p.property) Vs hVs blockA blockB J 1 m hmJ Q
      (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi cap p rfl zeta theta k
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootFinal -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Elementary absorption at the SAME depth, after both actual bounds. -/
theorem source_original_global_root_OLD_ABSORB434
    (L E : ℝ) (N : ℕ) (hL : 2≤L) (hN : 1≤N) (x y : ℂ)
    (hy : ‖y‖≤L^(-(E+1)*(N:ℝ))) (hd : ‖x-y‖≤L^(-(E+1)*(N:ℝ))) :
    ‖y‖≤L^(-E*(N:ℝ)) ∧ ‖x‖≤L^(-E*(N:ℝ)) := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1≤L := le_trans (by norm_num) hL
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hscale : 2≤L^(N:ℝ) := by
    apply hL.trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 hNr
  have heq : L^(N:ℝ)*L^(-(E+1)*(N:ℝ))=L^(-E*(N:ℝ)) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have htwo : 2*L^(-(E+1)*(N:ℝ))≤L^(-E*(N:ℝ)) := by
    calc
      _ ≤ L^(N:ℝ)*L^(-(E+1)*(N:ℝ)) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := heq
  constructor
  · exact hy.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith))
  · calc
      ‖x‖=‖(x-y)+y‖ := by congr 1; ring
      _ ≤ ‖x-y‖+‖y‖ := norm_add_le _ _
      _ ≤ 2*L^(-(E+1)*(N:ℝ)) := by linarith
      _ ≤ _ := htwo

/-- BOTH frozen original roots at the same fixed source parameter tuple.
OLD numerical injectivity is derived from original separation. -/
theorem eventually_source_original_global_root_BOTH434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr : 0 < rho) (hr1 : rho < 1) (hquarter : cfg.q0^(1/4:ℝ) < rho) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (k : ℤ) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck)
,
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    let cap := fun g => Fintype.card (BP g)
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi

    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let T := Nat.ceil (L^2)
    let A := (N+1)*Fintype.card G*(J+1+T)
    (‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ))) T‖ ≤
      L^(-E*(N:ℝ))) ∧
    (‖memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats cap cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ)))‖ ≤
      L^(-E*(N:ℝ))) := by
  have hE1 : 0<E+1 := by linarith
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hProj⟩ :=
    eventually_source_original_global_root_PROJECTED434 cfg gamma dscale (E+1) Cfreq c rho vmax c0 Ck
      hgamma hd hE1 hc hr hr1 hquarter hvmax hc0
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hProj,eventually_source_original_forest_SOURCE_OLD_MOVING434
    cfg J 1 m Cq Cxi hmJ (E+1) hE1.le,eventually_ge_atTop (2:ℝ)] with L hProj hOld hL
  dsimp only at hProj ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hProj⟩ := hProj
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap
  let SP := fun g : Option ι => {p : ℕ // p∈sourceOriginalActualSmallPrimeSets434 data g}
  let BP := fun g : G => {p : ℕ // p∈data.Tb g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let cap := fun g => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 data
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J 1 m hmJ Q
    (fun _ => h) (fun _ => h) xi
  have hHarmonic (g : G) : ∑ p : BP g,1/(p.val:ℝ)=data.Vbig g :=
    (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).trans (hVbig g).symm
  have hp := hProj x Y Hprime data sep hSmallUpper hVmax hSmallLower loB hiB hBigFull hLoLeHi
    hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap cap
  have hdisc := hOld data (source_original_global_root_BIG_INJECTIVE434 data sep)
    hHarmonic (fun g p => hTbLower g p.val p.property) blockA blockB Q hQcap
    (fun _ => h) (fun _ => h) xi (fun _ _ => hh) (fun _ _ => hh) hxi hxicap
    rho hr.ne' zeta theta k
  have hd' :
      ‖memorySourceRoot SP sm BP bm J 1 m pats cap cfg.q0 rho Vs data.Vbig K zeta theta k
          (Nat.ceil (L^(0.52:ℝ)))-
        sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J 1 m cap pats cfg.q0 rho Vs data.Vbig K
          zeta theta k (Nat.ceil (L^(0.52:ℝ))) T‖≤L^(-(E+1)*(N:ℝ)) := by
    simpa only [sourceOriginalActualSourceOLDDiscrepancy434,SP,BP,sm,bm,Vs,cap,pats,K,Q,h,xi,N,T]
      using hdisc
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hR : 0<Nat.ceil (L^(0.52:ℝ)) := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hLp _)
  have hN : 1≤N := by dsimp [N]; omega
  exact source_original_global_root_OLD_ABSORB434 L E N hL hN _ _ hp hd'
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootExpected -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Frozen expected root statement. Positive rho is DERIVED from the original
quarter-root gap, so no redundant extra analytic premise is exposed here.
The immutable expected-statements.md is checked separately field by field. -/
theorem eventually_source_original_global_root_EXPECTED434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr1 : rho < 1) (hquarter : cfg.q0^(1/4:ℝ) < rho) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
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
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (k : ℤ) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck)
,
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    let cap := fun g => Fintype.card (BP g)
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi

    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let T := Nat.ceil (L^2)
    let A := (N+1)*Fintype.card G*(J+1+T)
    (‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ))) T‖ ≤
      L^(-E*(N:ℝ))) ∧
    (‖memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats cap cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ)))‖ ≤
      L^(-E*(N:ℝ))) := by
  have hr : 0< rho := (Real.rpow_pos_of_pos cfg.hq0 (1/4:ℝ)).trans hquarter
  exact eventually_source_original_global_root_BOTH434 cfg gamma dscale E Cfreq c rho vmax c0 Ck
    hgamma hd hE hc hr hr1 hquarter hvmax hc0
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootTmaxData -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Change only the source multiplicity cap, leaving all physical constants fixed. -/
def sourceOriginalGlobalRootTmaxFixed434 (cfg : SourceComparisonFixed434) (t : ℕ) :
    SourceComparisonFixed434 := { cfg with tmax := t }

/-- Auxiliary data used only to invoke the root bound. All prime sets and masses
are definitionally unchanged. Endpoint multiplicity data are zeroed, since
those fields do not occur in either original physical root. -/
def sourceOriginalGlobalRootDataAtOne434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime) :
    SourceComparisonData434 ι G (sourceOriginalGlobalRootTmaxFixed434 cfg 1) x L Y Hprime :=
  { data with
    k := 0
    ts := fun _ => 0
    tb := fun _ => 0
    coef := fun _ => 0
    hk := by simp [sourceOriginalGlobalRootTmaxFixed434]
    hts := fun _ => Nat.zero_le _
    htb := fun _ => Nat.zero_le _
    hcoef := fun _ => by simp }

theorem source_original_global_root_TMAX_DATA_PRESERVES434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime) :
    (sourceOriginalGlobalRootDataAtOne434 data).S=data.S ∧
    (sourceOriginalGlobalRootDataAtOne434 data).Ts=data.Ts ∧
    (sourceOriginalGlobalRootDataAtOne434 data).Tb=data.Tb ∧
    (sourceOriginalGlobalRootDataAtOne434 data).Vs=data.Vs ∧
    (sourceOriginalGlobalRootDataAtOne434 data).Vsmall=data.Vsmall ∧
    (sourceOriginalGlobalRootDataAtOne434 data).Vbig=data.Vbig := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalRootTmax -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The full frozen root bounds, with multiplicity tmax quantified AFTER
all source parameters and the eventual L threshold. In particular tmax=1+m
can be chosen later without a circular cfg-before-m instantiation. -/
theorem eventually_source_original_global_root_TMAX_UNIFORM434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c rho vmax c0 Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c)
    (hr1 : rho < 1) (hquarter : cfg.q0^(1/4:ℝ) < rho) (hvmax : 0 < vmax) (hc0 : 0 < c0) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
    1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (tmax : ℕ)
      (data : SourceComparisonData434 ι G (sourceOriginalGlobalRootTmaxFixed434 cfg tmax) x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (hSmallUpper : ∀ g : Option ι,∀ p ∈ sourceOriginalActualSmallPrimeSets434 data g,
        (p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hVmax : ∀ g,data.Vbig g ≤ vmax)
      (hSmallLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ))
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
      (k : ℤ) (hk : k≠0)
      (hkCap : (k.natAbs:ℝ) ≤ L^Ck)
,
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    let cap := fun g => Fintype.card (BP g)
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi

    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let T := Nat.ceil (L^2)
    let A := (N+1)*Fintype.card G*(J+1+T)
    (‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ))) T‖ ≤
      L^(-E*(N:ℝ))) ∧
    (‖memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats cap cfg.q0 rho Vs data.Vbig K zeta theta k (Nat.ceil (L^(0.52:ℝ)))‖ ≤
      L^(-E*(N:ℝ))) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hRoot⟩ :=
    eventually_source_original_global_root_EXPECTED434 (sourceOriginalGlobalRootTmaxFixed434 cfg 1)
      gamma dscale E Cfreq c rho vmax c0 Ck hgamma hd hE hc hr1 hquarter hvmax hc0
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hRoot] with L hRoot
  dsimp only at hRoot ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hRoot⟩ := hRoot
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime tmax data instNZ sep hSmallUpper hVmax hSmallLower
    loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap
  let oneData := sourceOriginalGlobalRootDataAtOne434 data
  letI : ∀ g (p : {p : ℕ // p ∈ oneData.Tb g}), NeZero p.val := instNZ
  have hsep : SourceOriginalSource03GroupSeparation434 oneData :=
    ⟨sep.hTT,sep.hBB,sep.hTB⟩
  exact hRoot x Y Hprime oneData hsep hSmallUpper hVmax hSmallLower loB hiB hBigFull hLoLeHi
    hBigUpper hLoLarge hTbLower hVbig blockA blockB hBlocks hcountA hcountB
    zeta theta hZeta k hk hkCap
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceQSkipActualSourceDefinitions -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false

/-- Verbatim from SourceOriginalQ0GoodRestGeometry.lean. -/
noncomputable def sourceOriginalQ0Scale (r₀ : ℕ) : ℝ :=
  5/(11*(r₀:ℝ))

/-- Verbatim from SourceOriginalQActualGeometry.lean. -/
noncomputable def sourceOriginalQActualExponent (r₀ j : ℕ) : ℝ :=
  sourceOriginalQ0Scale r₀ / (2:ℝ)^j

/-- Verbatim from SourceShiftTwoClosedMacroBands.lean; both endpoints closed. -/
noncomputable def sourceClosedPrimeLogBand (L u v : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp (u*L)⌉₊ ⌊Real.exp (v*L)⌋₊).filter Nat.Prime

/-- Verbatim from SourceOriginalQActualGeometry.lean. -/
noncomputable def sourceOriginalQActualBands (r₀ jₓ : ℕ) (L : ℝ) :
    Fin (jₓ+1) → Finset ℕ := fun j =>
  sourceClosedPrimeLogBand L
    (sourceOriginalQActualExponent r₀ j.val)
    ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)
theorem sourceOriginalQActualBands_prime434
    (r d : ℕ) (L : ℝ) (j : Fin (d+1)) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands r d L j) : p.Prime := by
  exact (Finset.mem_filter.mp hp).2

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve

/-- Verbatim from SourcePhysicalSortedLabelEquiv.lean. -/
noncomputable def sourceOrderedLabels {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (i : Fin r) : List (B × Fin r) :=
  (((Finset.univ : Finset (B × Fin r)).erase (b,i)).toList.mergeSort
    (fun k l => decide (s l.1 < s k.1 ∨ s l.1=s k.1 ∧ k.2.val≤l.2.val)))

theorem source_ordered_labels_nodup {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (i : Fin r) :
    (sourceOrderedLabels r s b i).Nodup := by
  unfold sourceOrderedLabels
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem source_ordered_labels_mem {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (i : Fin r) (l : B × Fin r) :
    l ∈ sourceOrderedLabels r s b i ↔ l ≠ (b,i) := by
  unfold sourceOrderedLabels
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp
/-- Verbatim sorted index type and source label map. -/
noncomputable def sourceSortedLabelEquiv {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (i : Fin r) :
    Fin (sourceOrderedLabels r s b i).length ≃ {l : B × Fin r // l ≠ (b,i)} :=
  (List.Nodup.getEquiv (sourceOrderedLabels r s b i)
    (source_ordered_labels_nodup r s b i)).trans
      (Equiv.subtypeEquivRight (fun l => source_ordered_labels_mem r s b i l))

noncomputable def sourceOrderedPrimeBands {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (s : B → ℝ) (b : B) (i : Fin r) :
    Fin (sourceOrderedLabels r s b i).length → Finset ℕ :=
  fun z => Q (sourceSortedLabelEquiv r s b i z).val.1

noncomputable def sourceOrderedScales {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (s : B → ℝ) (b : B) (i : Fin r) :
    Fin (sourceOrderedLabels r s b i).length → ℝ :=
  fun z => s (sourceSortedLabelEquiv r s b i z).val.1

/-- Verbatim SourcePhysicalActualGlobalIntegral.lean original definitions. -/
noncomputable def sourceActualSortedScales (r d : ℕ) (L : ℝ) :
    Fin (d+1) → ℝ :=
  fun j => sourceOriginalPGroupScale r L j.val

noncomputable def sourceActualSortedQ (r d : ℕ) (L : ℝ)
    (b : Fin (d+1)) (i : Fin r) :=
  sourceOrderedPrimeBands r (sourceOriginalQActualBands r d L)
    (sourceActualSortedScales r d L) b i

noncomputable def sourceActualSortedFrequencyScales (r d : ℕ) (L : ℝ)
    (b : Fin (d+1)) (i : Fin r) :=
  sourceOrderedScales r (sourceActualSortedScales r d L) b i

end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualSortedQSkipPrimeCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- EXACT original T SourceNativeCoreDef constructor, now with all
sourceOriginalSorted Q bands and QSkip factorial/Fourier residual data
provided by their independently compiled native Lean4.34 source ports.
This constructs the original K-RESTRICTED alpha, literal residual
sourceEndpointFibre, q-character and both Mellin factors. No proxy
residual and no assumption of smallness. -/
noncomputable def sourceNativePrimeCore
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) : PrimeSlotCore where
  alpha := restrictSequence K alpha
  residual := sourceEndpointFibre
    (Finset.univ : Finset (OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ))
    orderedSkipProduct
    (fun a => sourceActualSortedFactorial r d *
      orderedSkipPhase (sourceActualSortedFrequencyScales r d L b slot) ξ a)
  q := q
  character := χ
  sigma₀ := σ₀
  sigma₁ := σ₁
  lo := ⌈Real.exp (sourceOriginalQActualExponent r b.val * L)⌉₊
  hi := ⌊Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r b.val)*L)⌋₊
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKRestrictedPrimeCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The EXACT original T sorted-Q/QSkip/factorial prime core commutes with
Dirichlet-character field replacement. Crucially, original `K`-restricted
alpha is preserved, unlike B491's global D20 alpha overwrite. -/
theorem source_native_B510_original_K_core_character_exact434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁ =
      sourceNativeWithCharacter434
        (sourceNativePrimeCore r d L b slot δ ξ K alpha 1 1 σ₀ σ₁) q χ := by
  rfl

/-- Actual original alpha is RESTRICTED to its original finite K, both
inside the same original T sorted-Q/QSkip factorial/residual core. -/
theorem source_native_B510_original_K_alpha_literal434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (m : ℕ) :
    (sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁).alpha m =
      if m ∈ K then alpha m else 0 := by
  rfl

/-- A TRUE original K-restricted D20 core still has original D20 support:
nonzero alpha in the T constructor implies m∈K and the unmodified
original centered D20 coefficient at m is nonzero. Nothing is inferred
from an artificially unrestricted/renormalized cofactor sequence. -/
theorem source_native_B510_original_K_D20_nonzero_support434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (m : ℕ)
    (hn : (sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁).alpha m ≠ 0) :
    m ∈ K ∧ sourceD20FullDelta Δ W y m ≠ 0 := by
  rw [source_native_B510_original_K_alpha_literal434] at hn
  by_cases hm : m ∈ K
  · simp only [if_pos hm] at hn
    refine ⟨hm,?_⟩
    exact_mod_cast hn
  · simp only [if_neg hm] at hn
    exact False.elim (hn rfl)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualQFrequencyContinuity -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The actual Parity(4.6) SOURCE history-dependent frequency
sigma_j = -xi_j/s_j - delta_j * sum_(i>j) xi_i/s_i
is jointly continuous in every real frequency, including cases
where the fixed denominator scale is zero. Boolean allocation gates
and the strict labelled order are fixed independent of xi. -/
@[fun_prop] theorem parity_original_actual_source_slot_frequency_continuous434
    {n : ℕ} (s : Fin n → ℝ) (δ : Fin n → Bool) (j : Fin n) :
    Continuous (fun ξ : Fin n → ℝ => sourceSlotFrequency s ξ δ j) := by
  classical
  by_cases h : δ j = true
  · simp only [sourceSlotFrequency,h,ite_true]
    apply Continuous.sub
    · fun_prop
    · apply continuous_finsetSum
      intro i hi
      by_cases hij : j < i
      · simp only [hij,ite_true]
        fun_prop
      · simp only [hij,ite_false]
        fun_prop
  · have hf : δ j = false := by
      cases hb : δ j <;> simp_all
    simp only [sourceSlotFrequency,hf,Bool.false_eq_true,ite_false,sub_zero]
    fun_prop

/-- The exact original natural prime product orderedSkipPhase in the
full source B509 residual is continuous in all ORIGINAL Fourier
variables; its source division, prime logarithms and historical
delta gates are kept unchanged. -/
@[fun_prop] theorem parity_original_actual_ordered_skip_phase_continuous434
    {n : ℕ} {Q : Fin n → Finset ℕ} (s : Fin n → ℝ)
    (δ : Fin n → Bool) (a : OrderedQSkip n Q δ) :
    Continuous (fun ξ : Fin n → ℝ => orderedSkipPhase s ξ a) := by
  unfold orderedSkipPhase
  fun_prop

/-- The same actual source natural endpoint-value fibre, formed from
all repeated original ordered-QSkip prime tuples and their genuine
factorial Fourier coefficient, is continuous in every original xi.
No arbitrary measurable replacement of a source residual is used. -/
theorem parity_original_actual_source_endpoint_fibre_continuous434
    {n : ℕ} {Q : Fin n → Finset ℕ} (s : Fin n → ℝ)
    (δ : Fin n → Bool) (g : OrderedQSkip n Q δ → ℕ)
    (c : ℂ) (v : ℕ) :
    Continuous (fun ξ : Fin n → ℝ =>
      sourceEndpointFibre
        (Finset.univ : Finset (OrderedQSkip n Q δ)) g
        (fun a => c * orderedSkipPhase s ξ a) v) := by
  classical
  unfold sourceEndpointFibre
  apply continuous_finsetSum
  intro a ha
  exact continuous_const.mul
    (parity_original_actual_ordered_skip_phase_continuous434 s δ a)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualQCoreResidualContinuity -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- The FULL original Q-factorial-labelled actual B509 prime-slot
residual, with real historical all-index Fourier frequencies and
literal ordered-QSkip source carrier, is jointly continuous in all
N real coordinates. The character and rough first coefficients are
unchanged: their independence from xi is definitional in
`sourceNativePrimeCore` itself. This discharges the real source
measurability obligation at the residual layer of Parity (4.7). -/
theorem parity_original_actual_native_prime_core_residual_continuous434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (v : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels r
        (sourceActualSortedScales r d L) b slot).length → ℝ =>
      (sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁).residual v) := by
  let s := sourceActualSortedFrequencyScales r d L b slot
  change Continuous (fun ξ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → ℝ =>
    sourceEndpointFibre
      (Finset.univ : Finset (OrderedQSkip
        (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
        (sourceActualSortedQ r d L b slot) δ))
      orderedSkipProduct
      (fun a => (sourceActualSortedFactorial r d : ℂ) * orderedSkipPhase s ξ a) v)
  exact parity_original_actual_source_endpoint_fibre_continuous434
    s δ orderedSkipProduct (sourceActualSortedFactorial r d) v

/-- Strong measurability of the genuine original QSkip residual under
source Fourier Lebesgue measure, not an abstract Fδ(xi) surrogate. -/
theorem parity_original_actual_native_prime_core_residual_ae_measurable434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (v : ℕ) :
    AEStronglyMeasurable (fun ξ : Fin (sourceOrderedLabels r
        (sourceActualSortedScales r d L) b slot).length → ℝ =>
      (sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁).residual v)
      (volume : Measure (Fin (sourceOrderedLabels r
        (sourceActualSortedScales r d L) b slot).length → ℝ)) := by
  exact (parity_original_actual_native_prime_core_residual_continuous434
    r d L b slot δ K alpha q χ σ₀ σ₁ v).aestronglyMeasurable
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKShiftedCoprimeCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL sorted-Q/QSkip factorial/fourier PrimeSlotCore, with
its TRUE finite K-restricted centered D20 alpha (not an unrestricted
replacement), has EXACT coprime m,t cofactor expansion at the physical
integer shift z -> z+2k when |2k|≤W. The RHS contains the full original
p-slot/Q-band/residual/Mellin character factors and makes no analytic
saving assertion. Right endpoint may have any ORIGINAL PrimeSlotCore. -/
theorem source_native_B514_original_K_D20_shifted_QP_coprime_exact434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) (H : PrimeSlotCore)
    (z : ℕ) (k : ℤ) (hz : z ≠ 0)
    (hk : k ≠ 0) (hpos : 0 < (z:ℤ)+2*k)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    star (primeSlotCoreValue P Fcore z) * primeSlotCoreValue P H zR =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      if Nat.Coprime m t then
        star (sourceNativePrimeCoreCofactor434 P Fcore z m) *
          sourceNativePrimeCoreCofactor434 P H zR t
      else 0 := by
  dsimp only
  let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  have hzR : zR ≠ 0 := by
    dsimp [zR]
    omega
  have hl : primeSlotCoreValue P Fcore z =
      ∑ m ∈ nsL.divisors, sourceNativePrimeCoreCofactor434 P Fcore z m :=
    source_native_B491_full_QP_core_cofactor_expansion434 P Fcore z
  have hr : primeSlotCoreValue P H zR =
      ∑ t ∈ nsR.divisors, sourceNativePrimeCoreCofactor434 P H zR t :=
    source_native_B491_full_QP_core_cofactor_expansion434 P H zR
  rw [hl,hr,star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases ha : Fcore.alpha m = 0
  · rw [source_native_B491_QP_cofactor_alpha_zero434 P Fcore z m ha]
    simp
  · have hD20 : sourceD20FullDelta Δ W y m ≠ 0 :=
      (source_native_B510_original_K_D20_nonzero_support434
        r d L b slot δ ξ K Δ W y q χ σ₀ σ₁ m ha).2
    have hmz : m ∣ z :=
      (Nat.mem_divisors.mp hm).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) z hz)
    have htz : t ∣ zR :=
      (Nat.mem_divisors.mp ht).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) zR hzR)
    have hc : Nat.Coprime m t :=
      Green64Analytic.CorrelationSquare.source_original_B489_actual_D20_shifted_cofactor_coprime434
        Δ W y hWy m t z k hD20 hk hsmall hpos hmz htz
    rw [if_pos hc]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKPhysicalCoprimeSummand -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact T-native physical cofactor summand with BOTH original source
and target cores unmodified. The source retains its literal sorted-QSkip
factorial/Fourier residual and original finite K-restricted centered D20
coefficient; the target retains its separate actual Q/P residual. -/
noncomputable def sourceNativeB515ProjectedCoprimeTerm434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) : ℂ :=
  let zR := ((z:ℤ)+2*k).toNat
  if 0 < (z:ℤ)+2*k then
    if Nat.Coprime m t then
      psi ((z:ℝ)/Z)/(z:ℂ) *
      imaginaryPower z a1 * imaginaryPower zR a2 *
      star (sourceNativePrimeCoreCofactor434 P F z m) *
      sourceNativePrimeCoreCofactor434 P H zR t *
      (sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P zR : ℝ) *
      ((((1-groupSign P true z)/2) *
        ((1-groupSign P true zR)/2)) : ℝ)
    else 0
  else 0

/-- Full literal original physical source T four-sign projected summand
at z and z+2k equals the COPRIME cofactor sum with the exact original
K-restricted sorted-QSkip/factorial source alpha, no global D20 override.
The original shift2k divisor obstruction is proved by B514. -/
theorem source_native_B515_K_restricted_physical_summand_coprime_exact434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (H : PrimeSlotCore)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ) (z : ℕ)
    (hz : z ≠ 0) (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    sourceCorrelationBaseKernel c g P Fcore H Z a1 a2 (2*k) psi z *
      ((((1-groupSign P true z)/2) *
        ((1-groupSign P true zR)/2)) : ℝ) =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      sourceNativeB515ProjectedCoprimeTerm434 c g P Fcore H
        Z a1 a2 k psi z m t := by
  dsimp only
  let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  by_cases hp : 0 < (z:ℤ)+2*k
  · have hCore := source_native_B514_original_K_D20_shifted_QP_coprime_exact434
      P r d L b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ H z k hz hk hp hsmall
    change star (primeSlotCoreValue P Fcore z) * primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P Fcore z m) *
          sourceNativePrimeCoreCofactor434 P H zR t else 0 at hCore
    let pref : ℂ := psi ((z:ℝ)/Z)/(z:ℂ) *
      imaginaryPower z a1 * imaginaryPower zR a2
    let w : ℂ := ((sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P zR : ℝ):ℂ)
    let proj : ℂ := (((1-groupSign P true z)/2) *
      ((1-groupSign P true zR)/2) : ℝ)
    have hPhysical :
      sourceCorrelationBaseKernel c g P Fcore H Z a1 a2 (2*k) psi z *
        (((1-groupSign P true z)/2) *
          ((1-groupSign P true zR)/2) : ℝ) =
      pref * (star (primeSlotCoreValue P Fcore z) *
              primeSlotCoreValue P H zR) * w * proj := by
      unfold sourceCorrelationBaseKernel
      simp only [if_pos hp]
      dsimp only [pref,w,proj,zR,Fcore]
      ring
    rw [hPhysical,hCore]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [sourceNativeB515ProjectedCoprimeTerm434,zR]
    rw [if_pos hp]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      dsimp only [pref,w,proj]
      ring
    · simp only [if_neg hc]
      ring
  · simp only [sourceNativeB515ProjectedCoprimeTerm434,
      sourceCorrelationBaseKernel,if_neg hp,zero_mul,Finset.sum_const_zero]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKFullShiftedProjectedCorrelation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- COMPLETE position-summed original T projected Q/P physical
correlation z->z+2k with ORIGINAL finite K-restricted, QSkip/factorial
source-native alpha. Its exact cofactor expansion contains only coprime
m,t; no original p-slot, residual, marked weight, Fourier or parity
factor is dropped, and the target may be a distinct physical core. -/
theorem source_native_B516_K_restricted_full_projected_coprime_exact434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (H : PrimeSlotCore)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let Fcore := sourceNativePrimeCore r d L b slot δ ξ K
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁
    sourceCorrelationProjected c g P Fcore H
        Z a1 a2 bPsi (2*k) psi =
      ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
        ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
        ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
             (((z:ℤ)+2*k).toNat)).divisors,
          sourceNativeB515ProjectedCoprimeTerm434 c g P Fcore H
            Z a1 a2 k psi z m t := by
  dsimp only
  unfold sourceCorrelationProjected
  apply Finset.sum_congr rfl
  intro z hz
  have hz0 : z ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hz).1
  change sourceCorrelationBaseKernel c g P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σ₀ σ₁)
      H Z a1 a2 (2*k) psi z *
       ((((1-groupSign P true z)/2) *
         ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2)):ℝ) = _
  exact source_native_B515_K_restricted_physical_summand_coprime_exact434
    c g P r d L b slot δ ξ K Δ W y hWy q χ σ₀ σ₁ H
    Z a1 a2 k psi z hz0 hk hsmall
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKPhysicalCharacterFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- For BOTH actual original T sourceNativePrimeCore constructors, with
independent δ/ξ/QSkip data and finite cofactor sets KF,KG, the full
physical shifted 2k m,t cofactor amplitude factors as χ̄(m)χ(t) times
the genuinely K-restricted character-free amplitude, including every
original source/target prime slot, residual, Mellin, marked and parity
factor. No global D20 alpha replacement nor pre-square averaging. -/
theorem source_native_B517_original_K_QP_shifted_character_factor434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) :
    let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
    let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
    let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
    let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
    sourceNativeB515ProjectedCoprimeTerm434 c g P Fχ Gχ
      Z a1 a2 k psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB515ProjectedCoprimeTerm434 c g P F0 G0
        Z a1 a2 k psi z m t := by
  dsimp only
  let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
  let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
  change sourceNativeB515ProjectedCoprimeTerm434 c g P
      (sourceNativeWithCharacter434 F0 q χ)
      (sourceNativeWithCharacter434 G0 q χ)
      Z a1 a2 k psi z m t =
    sourceNativeB496PhysicalPairCharacter434 q m t χ *
      sourceNativeB515ProjectedCoprimeTerm434 c g P F0 G0
      Z a1 a2 k psi z m t
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB515ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [source_native_B495_QP_cofactor_character_factor434 P F0 q χ z m,
          source_native_B495_QP_cofactor_character_factor434 P G0 q χ
            (((z:ℤ)+2*k).toNat) t,star_mul]
      have hF0 : sourceNativeWithoutCharacter434 F0 = F0 := rfl
      have hG0 : sourceNativeWithoutCharacter434 G0 = G0 := rfl
      rw [hF0,hG0]
      unfold sourceNativeB496PhysicalPairCharacter434
      ring
    · simp [sourceNativeB515ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB515ProjectedCoprimeTerm434,hp]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKActivePhysicalTriples -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The ORIGINAL physical shifted-position T triple domain is the SAME
native dependent Sigma(z,m,t) as B502, but BOTH cofactor supports retain
the literal original KF,KG restrictions of sourceNativePrimeCore. -/
noncomputable def sourceNativeB518OriginalKActiveTriples434
    (g : ℕ) (P : Fin g → Finset ℕ)
    (Z bPsi : ℝ) (k : ℤ) (KF KG : Finset ℕ) (Δ W y : ℝ) :
    Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (sourceNativeB502FullPhysicalTriples434 g P Z bPsi k).filter
    (fun s =>
      (s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
      (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0))

/-- Exact original physical projected Q/P term vanishes when the actual
K-restricted SOURCE PrimeSlotCore alpha(m) is zero. No assumptions on
character, residual, cofactor or Mellin phase. -/
theorem source_native_B518_QP_physical_term_zero_left434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) (ha : F.alpha m = 0) :
    sourceNativeB515ProjectedCoprimeTerm434 c g P F H
      Z a1 a2 k psi z m t = 0 := by
  have hco := source_native_B491_QP_cofactor_alpha_zero434 P F z m ha
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB515ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [hco]
      simp
    · simp [sourceNativeB515ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB515ProjectedCoprimeTerm434,hp]

/-- Exact original physical projected Q/P term vanishes when the actual
K-restricted TARGET PrimeSlotCore alpha(t) is zero. -/
theorem source_native_B518_QP_physical_term_zero_right434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) (ha : H.alpha t = 0) :
    sourceNativeB515ProjectedCoprimeTerm434 c g P F H
      Z a1 a2 k psi z m t = 0 := by
  have hco := source_native_B491_QP_cofactor_alpha_zero434 P H
    (((z:ℤ)+2*k).toNat) t ha
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB515ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [hco]
      simp
    · simp [sourceNativeB515ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB515ProjectedCoprimeTerm434,hp]

/-- Literal original K-restricted source and target Q/P cofactor term
is ZERO outside the exact finite active KF×KG/cofactor-Delta support.
The ambient set is a genuine z-dependent divisor Sigma, not a cofactor
rectangle; no lost pattern, physical phase, divisor or sign sector. -/
theorem source_native_B518_actual_K_zero_outside_triples434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (s : Σ _ : ℕ, ℕ × ℕ)
    (hs : s ∈ sourceNativeB502FullPhysicalTriples434 g P Z bPsi k)
    (hn : s ∉ sourceNativeB518OriginalKActiveTriples434
      g P Z bPsi k KF KG Δ W y) :
    sourceNativeB515ProjectedCoprimeTerm434 c g P
      (sourceNativePrimeCore r d L b slot δF ξF KF
        (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1)
      (sourceNativePrimeCore r d L b slot δG ξG KG
        (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1)
      Z a1 a2 k psi s.1 s.2.1 s.2.2 = 0 := by
  let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
  let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
  have hNo : ¬ ((s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
       (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0)) := by
    intro both
    exact hn (Finset.mem_filter.mpr ⟨hs,both⟩)
  by_cases hF : s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0
  · have hG : Gχ.alpha s.2.2 = 0 := by
      by_contra hNon
      exact hNo ⟨hF, source_native_B510_original_K_D20_nonzero_support434
        r d L b slot δG ξG KG Δ W y q χ σG0 σG1 s.2.2 hNon⟩
    exact source_native_B518_QP_physical_term_zero_right434
      c g P Fχ Gχ Z a1 a2 k psi s.1 s.2.1 s.2.2 hG
  · have hF0 : Fχ.alpha s.2.1 = 0 := by
      by_contra hNon
      exact hF (source_native_B510_original_K_D20_nonzero_support434
        r d L b slot δF ξF KF Δ W y q χ σF0 σF1 s.2.1 hNon)
    exact source_native_B518_QP_physical_term_zero_left434
      c g P Fχ Gχ Z a1 a2 k psi s.1 s.2.1 s.2.2 hF0
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKFullPhysicalTripleSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Complete original sorted-QSkip/factorial SOURCE+TARGET physical
projected Q/P correlation at the true integer shift 2k equals an EXACT
coherent sum over the TRUE dependent physical (z,m,t) divisor triples
with both ORIGINAL finite KF,KG centered D20 cofactor supports. The support
restriction is lossless: every omitted native core term is identically zero.
No rectangular substitute, fake normalisation or character average. -/
theorem source_native_B519_actual_K_full_physical_shifted_triples_exact434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
    let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
    let S := sourceNativeB518OriginalKActiveTriples434
      g P Z bPsi k KF KG Δ W y
    sourceCorrelationProjected c g P Fχ Gχ
      Z a1 a2 bPsi (2*k) psi =
    ∑ s ∈ S, sourceNativeB515ProjectedCoprimeTerm434 c g P Fχ Gχ
      Z a1 a2 k psi s.1 s.2.1 s.2.2 := by
  dsimp only
  let Fχ := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σF0 σF1
  let Gχ := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) q χ σG0 σG1
  let Zset := Finset.Icc 1 ⌊bPsi*Z⌋₊
  let D : ℕ → Finset (ℕ×ℕ) := fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
       (((z:ℤ)+2*k).toNat)).divisors
  let Sfull : Finset (Σ _ : ℕ, ℕ×ℕ) := Zset.sigma D
  let S := Sfull.filter (fun s =>
    (s.2.1 ∈ KF ∧ sourceD20FullDelta Δ W y s.2.1 ≠ 0) ∧
    (s.2.2 ∈ KG ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0))
  let B : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB515ProjectedCoprimeTerm434 c g P Fχ Gχ
      Z a1 a2 k psi s.1 s.2.1 s.2.2
  have hOriginal := source_native_B516_K_restricted_full_projected_coprime_exact434
    c g P r d L b slot δF ξF KF Δ W y hWy q χ σF0 σF1
    Gχ Z a1 a2 bPsi k psi hk hsmall
  have hSigma : (∑ z ∈ Zset, ∑ v ∈ D z, B ⟨z,v⟩) =
      ∑ s ∈ Sfull, B s :=
    (Finset.sum_sigma Zset D B).symm
  have hZero (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ Sfull)
      (hsnot : s ∉ S) : B s = 0 :=
    source_native_B518_actual_K_zero_outside_triples434
      c g P r d L b slot δF δG ξF ξG KF KG Δ W y q χ
      σF0 σF1 σG0 σG1 Z a1 a2 bPsi k psi s hs hsnot
  have hFilter : (∑ s ∈ S, B s) = ∑ s ∈ Sfull, B s :=
    Finset.sum_subset (Finset.filter_subset _ _) hZero
  change sourceCorrelationProjected c g P Fχ Gχ
    Z a1 a2 bPsi (2*k) psi = ∑ s ∈ S, B s
  calc
    _ = ∑ z ∈ Zset,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors, B ⟨z,(m,t)⟩ := hOriginal
    _ = ∑ z ∈ Zset, ∑ v ∈ D z, B ⟨z,v⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Finset.sum_product
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors
        (fun v : ℕ×ℕ => B ⟨z,v⟩)).symm
    _ = ∑ s ∈ Sfull, B s := hSigma
    _ = ∑ s ∈ S, B s := hFilter.symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## OriginalKFullNativeRatioRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- FULL original T sorted-Q/QSkip/factorial source and target cores,
with their LITERAL independent finite cofactor supports KF,KG and
true signed D20 centered coefficients, at the integer physical shift 2k:
the normalized post-square character RMS equals the sum of nonnegative
squared COHERENT native Q/P physical amplitudes on the actually occupied
cofactor ratio fibers t/m mod |k|. All physical z positions, dependent
m,t divisor lists, QSkip residuals, marked weights, four parity signs,
Mellin phases and Fourier Schwartz cutoff are preserved exactly.
The only arithmetic assumptions are genuine original W≤y, k≠0 and
|2k|≤W; there is no false unrestricted-alpha replacement or extra q≤W.
This is an exact identity, NOT a nontrivial estimate on the ratio fibers. -/
theorem source_native_B520_K_restricted_original_QP_character_RMS_ratio_fibers434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δF δG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξF ξG : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (KF KG : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (σF0 σF1 σG0 σG1 : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
    let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
      (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
    let S := sourceNativeB518OriginalKActiveTriples434
      g P Z bPsi k KF KG Δ W y
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB515ProjectedCoprimeTerm434 c g P F0 G0
        Z a1 a2 k psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceCorrelationProjected c g P
          (sourceNativePrimeCore r d L b slot δF ξF KF
            (fun n => (sourceD20FullDelta Δ W y n:ℂ))
            k.natAbs χ σF0 σF1)
          (sourceNativePrimeCore r d L b slot δG ξG KG
            (fun n => (sourceD20FullDelta Δ W y n:ℂ))
            k.natAbs χ σG0 σG1)
          Z a1 a2 bPsi (2*k) psi‖^2) =
      ∑ t ∈ S.image ratio,
        ‖∑ s ∈ S.filter (fun s => ratio s = t), base s‖^2 := by
  dsimp only
  let F0 := sourceNativePrimeCore r d L b slot δF ξF KF
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σF0 σF1
  let G0 := sourceNativePrimeCore r d L b slot δG ξG KG
    (fun n => (sourceD20FullDelta Δ W y n:ℂ)) 1 1 σG0 σG1
  let S := sourceNativeB518OriginalKActiveTriples434
    g P Z bPsi k KF KG Δ W y
  let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB515ProjectedCoprimeTerm434 c g P F0 G0
      Z a1 a2 k psi s.1 s.2.1 s.2.2
  let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
    (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
  have hnk : k.natAbs ≤ (2*k).natAbs := by
    rw [Int.natAbs_mul]
    change k.natAbs ≤ 2*k.natAbs
    omega
  have hqW : ((k.natAbs:ℕ):ℝ) ≤ W :=
    (by exact_mod_cast hnk : ((k.natAbs:ℕ):ℝ) ≤ ((2*k).natAbs:ℝ)).trans hsmall
  have hUnit (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ S) :
      IsUnit (s.2.1 : ZMod k.natAbs) := by
    have hn := (Finset.mem_filter.mp hs).2.1.2
    exact source_native_B497_actual_D20_nonzero_unit_mod_q434
      Δ W y hWy s.2.1 hn k.natAbs (Int.natAbs_pos.mpr hk) hqW
  have hCross : ∀ s ∈ S, ∀ v ∈ S,
      IsUnit (((v.2.1*s.2.2:ℕ):ZMod k.natAbs)) := by
    intro s hs v hv
    have hmp := (Finset.mem_filter.mp hv).2.1.2
    have ht := (Finset.mem_filter.mp hs).2.2.2
    exact source_native_B497_true_shift_q_cross_cofactor_isUnit434
      Δ W y hWy k hk hqW v.2.1 s.2.2 hmp ht
  have hFactor (χ : DirichletCharacter ℂ k.natAbs)
      (s : Σ _ : ℕ, ℕ×ℕ) :
      sourceNativeB515ProjectedCoprimeTerm434 c g P
        (sourceNativePrimeCore r d L b slot δF ξF KF
          (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σF0 σF1)
        (sourceNativePrimeCore r d L b slot δG ξG KG
          (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σG0 σG1)
        Z a1 a2 k psi s.1 s.2.1 s.2.2 =
      base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hh := source_native_B517_original_K_QP_shifted_character_factor434
      c g P r d L b slot δF δG ξF ξG KF KG Δ W y
      k.natAbs χ σF0 σF1 σG0 σG1 Z a1 a2 k psi s.1 s.2.1 s.2.2
    change _ = sourceNativeB496PhysicalPairCharacter434
      k.natAbs s.2.1 s.2.2 χ * base s at hh
    rw [hh]
    ring
  have hWhole (χ : DirichletCharacter ℂ k.natAbs) :
      sourceCorrelationProjected c g P
        (sourceNativePrimeCore r d L b slot δF ξF KF
          (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σF0 σF1)
        (sourceNativePrimeCore r d L b slot δG ξG KG
          (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σG0 σG1)
        Z a1 a2 bPsi (2*k) psi =
      ∑ s ∈ S, base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    have hh := source_native_B519_actual_K_full_physical_shifted_triples_exact434
      c g P r d L b slot δF δG ξF ξG KF KG Δ W y hWy
      k.natAbs χ σF0 σF1 σG0 σG1 Z a1 a2 bPsi k psi hk hsmall
    calc
      _ = ∑ s ∈ S,
        sourceNativeB515ProjectedCoprimeTerm434 c g P
          (sourceNativePrimeCore r d L b slot δF ξF KF
            (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σF0 σF1)
          (sourceNativePrimeCore r d L b slot δG ξG KG
            (fun n => (sourceD20FullDelta Δ W y n:ℂ)) k.natAbs χ σG0 σG1)
          Z a1 a2 k psi s.1 s.2.1 s.2.2 := hh
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hFactor χ s
  have hGram := source_native_B501_finite_physical_character_RMS_residue_only434
    S k.natAbs (Int.natAbs_pos.mpr hk)
    (fun s => s.2.1) (fun s => s.2.2) base hCross
  have hFibers := source_native_B506_finite_ratio_fiber_square_identity434
    S ratio base
  have hCong (s v : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ S) (hv : v ∈ S) :
      (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
       ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) ↔ ratio s = ratio v :=
    source_native_B505_original_QP_cross_residue_iff_ratio434
      k.natAbs s.2.1 s.2.2 v.2.1 v.2.2 (hUnit s hs) (hUnit v hv)
  calc
    _ = ∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖∑ s ∈ S,
          base s * sourceNativeB496PhysicalPairCharacter434
            k.natAbs s.2.1 s.2.2 χ‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hWhole χ]
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) then
        (star (base s)*base v).re else 0 := hGram
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if ratio s = ratio v then (star (base s)*base v).re else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      by_cases he : (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs))
      · have hr := (hCong s v hs hv).mp he
        simp only [if_pos he,if_pos hr]
      · have hr : ratio s ≠ ratio v :=
          fun h => he ((hCong s v hs hv).mpr h)
        simp only [if_neg he,if_neg hr]
    _ = ∑ t ∈ S.image ratio,
      ‖∑ s ∈ S.filter (fun s => ratio s = t), base s‖^2 := by
      simpa only using hFibers
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FockOutsidePrimeCoreBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The ORIGINAL Fock/physical endpoint `sourceOutsidePart` and the
ORIGINAL T native Q/P core `sourceOriginalOrdinaryPart` are literally
the same integer, for EVERY natural endpoint n, including repeated prime
factor multiplicities. This removes a real source↔T representation seam
without taking a bound or suppressing any sign/prime factor. -/
theorem source_native_B521_fock_outside_eq_T_original_ordinary434
    (P : Finset ℕ) (n : ℕ) :
    sourceOutsidePart P n = sourceOriginalOrdinaryPart P n := by
  unfold sourceOutsidePart sourceOriginalOrdinaryPart
  have hset : (n.primeFactors.filter (fun p => p ∉ P)) =
      (n.primeFactors \ P) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_sdiff]
  rw [hset]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FockPhysicalMellinTwistBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Original physical Fock ordinary sourceCore uses sourceUnitTwist,
whereas the original T shifted PrimeSlotCore uses imaginaryPower.
For each TRUE positive endpoint/cofactor/prime, they are EXACTLY the
same complex Mellin phase. This is an exact identity, not an estimate;
no branch of Complex.log is mishandled at a nonpositive endpoint. -/
theorem source_native_B522_fock_sourceUnitTwist_eq_T_imaginaryPower434
    (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    sourceUnitTwist n σ = imaginaryPower n σ := by
  unfold sourceUnitTwist imaginaryPower
  have hn0 : (n:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hPos : 0 ≤ (n:ℝ) := by positivity
  have hcast : (n:ℂ) = ((n:ℝ):ℂ) := by norm_cast
  have hlog : Complex.log (n:ℂ) = ((Real.log (n:ℝ)):ℂ) := by
    rw [hcast]
    exact (Complex.ofReal_log hPos).symm
  rw [hlog]
  congr 1
  push_cast
  ring
end Green64Analytic.ShiftTwoTerminal

end

end

