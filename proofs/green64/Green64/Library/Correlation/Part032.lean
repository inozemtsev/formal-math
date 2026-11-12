module

public import Green64.Library.Correlation.GlobalRootScalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part030
public import Green64.Library.Weights.UnfilteredForestListedRows
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib
public import Green64.Library.Weights.Part020
public import Green64.Library.Weights.Part019

@[expose] public section

/-!
# Correlation / Part032

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGlobalRootRates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- All scalar rank conditions are eventual after their fixed constants.
In particular neither the early local saving nor J is changed here. -/
theorem eventually_source_original_global_root_RATES434
    (c v e Cv Cb K : ℝ) (hc : 0<c) (hv : 0<v) :
    ∀ᶠ L : ℝ in atTop,
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    2≤L ∧ 5≤N ∧ Cv≤(N:ℝ) ∧
    (8+2*K)*L^(-c/2)≤1 ∧
    (∀ A : ℕ,(A:ℝ)≤L^4 →
      (A:ℝ)^2*(2/(v*Real.exp (L^c)))≤Real.exp (-(L^c)/2)) ∧
    2*(e+Cb+Cv+4)*Real.log L≤L^(c/2) := by
  let C := 2/v
  let D := max 0 (2*(e+Cb+Cv+4))
  have hC : 0<C := by dsimp [C]; positivity
  have hD : 0≤D := le_max_left _ _
  have hpow (a B : ℝ) (ha : 0<a) : ∀ᶠ L : ℝ in atTop,B≤L^a :=
    (tendsto_atTop.1 (tendsto_rpow_atTop ha)) B
  filter_upwards [eventually_ge_atTop (2:ℝ),
    hpow (0.52:ℝ) (max 5 Cv) (by norm_num),
    hpow (c/2) (8+2*K) (by positivity),
    hpow c (4*max 0 (Real.log C)) hc,
    hpow (3*c/4) (128/c) (by positivity),
    hpow (c/4) (4*D/c) (by positivity)]
    with L hL hNlarge hcut hCexp hlogexp hDexp
  dsimp only
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1≤L := le_trans (by norm_num) hL
  have hl : 0≤Real.log L := Real.log_nonneg hL1
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  have hNlower : 2*L^(0.52:ℝ)≤(N:ℝ) := by
    have hh := Nat.le_ceil (L^(0.52:ℝ))
    dsimp only [N]
    push_cast
    linarith
  have hN5 : 5≤N := by
    have hn : (5:ℝ)≤N := by linarith [le_max_left (5:ℝ) Cv]
    exact_mod_cast hn
  have hNCv : Cv≤(N:ℝ) := by
    linarith [le_max_right (5:ℝ) Cv,le_max_left (5:ℝ) Cv]
  refine ⟨hL,hN5,hNCv,?_,?_,?_⟩
  · have hpos : 0<L^(c/2) := Real.rpow_pos_of_pos hLp _
    rw [show -c/2= -(c/2) by ring,Real.rpow_neg hLp.le,←div_eq_mul_inv]
    exact (div_le_one hpos).mpr hcut
  · intro A hA
    have hlog : Real.log L≤(4/c)*L^(c/4) := by
      have hh := Real.log_le_rpow_div hLp.le (by positivity : 0<c/4)
      convert hh using 1 <;> field_simp <;> ring
    have hlogmul : 8*Real.log L≤L^c/4 := by
      have hh := (div_le_iff₀ hc).mp hlogexp
      have hprod : L^(3*c/4)*L^(c/4)=L^c := by
        rw [←Real.rpow_add hLp]; congr 1; ring
      have hsmall : 128*L^(c/4)≤ c*L^c := by
        calc
          _ ≤ (L^(3*c/4)*c)*L^(c/4) :=
            mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hLp.le (c/4))
          _ = c*(L^(3*c/4)*L^(c/4)) := by ring
          _ = _ := by rw [hprod]
      have hscale : 8*Real.log L≤32*L^(c/4)/c := by
        calc
          _ ≤ 8*((4/c)*L^(c/4)) := mul_le_mul_of_nonneg_left hlog (by norm_num)
          _ = _ := by ring
      have h2 := (le_div_iff₀ hc).mp hscale
      have hres : c*(8*Real.log L)≤ c*(L^c/4) := by nlinarith
      by_contra hbad
      have hp := mul_pos hc (sub_pos.mpr (lt_of_not_ge hbad))
      nlinarith
    have hlogC : Real.log C≤L^c/4 := by
      linarith [le_max_right (0:ℝ) (Real.log C)]
    have hexp : L^8*(2/(v*Real.exp (L^c))) =
        Real.exp (8*Real.log L+Real.log C-L^c) := by
      rw [Real.exp_sub,Real.exp_add,Real.exp_log hC]
      have he : Real.exp (8*Real.log L)=L^8 := by
        rw [←Real.rpow_natCast L 8,Real.rpow_def_of_pos hLp]
        congr 1
        ring
      rw [he]
      dsimp only [C]
      field_simp
    have hA2 : (A:ℝ)^2≤L^8 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg A : (0:ℝ)≤A) hA 2
      convert h using 1 <;> ring
    calc
      _ ≤ L^8*(2/(v*Real.exp (L^c))) := mul_le_mul_of_nonneg_right hA2 (by positivity)
      _ = _ := hexp
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hlog : Real.log L≤(4/c)*L^(c/4) := by
      have hh := Real.log_le_rpow_div hLp.le (by positivity : 0<c/4)
      convert hh using 1 <;> field_simp <;> ring
    have hprod : L^(c/4)*L^(c/4)=L^(c/2) := by
      rw [←Real.rpow_add hLp]; congr 1; ring
    have h1 := mul_le_mul_of_nonneg_left hlog hD
    have h2 := mul_le_mul_of_nonneg_right hDexp (Real.rpow_nonneg hLp.le (c/4))
    rw [hprod] at h2
    have h0 := mul_le_mul_of_nonneg_right (le_max_right (0:ℝ) (2*(e+Cb+Cv+4))) hl
    apply h0.trans
    apply h1.trans
    convert h2 using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootSlotSigns -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {E Addr A : Type} [Fintype E] [Fintype Addr] [DecidableEq Addr]
variable [Fintype A] [DecidableEq A]

/-- One independent field for each edge. Centering belongs to each
potential address and is independent of any performed-path enumeration. -/
def sourceOriginalRootCenteredSlot434
    (left right : E → Addr) (sentinel : Addr → A)
    (h : E → A → Bool) (a : Addr) (x : A) : ℂ :=
  ∏ e : E,
    (if left e=a then sourceOriginalRootSign434 (h e x) *
      sourceOriginalRootSign434 (h e (sentinel a)) else 1) *
    (if right e=a then sourceOriginalRootSign434 (h e x) *
      sourceOriginalRootSign434 (h e (sentinel a)) else 1)

theorem source_original_root_CENTERED_SLOT_UNIT434
    (left right : E → Addr) (sentinel : Addr → A)
    (h : E → A → Bool) (a : Addr) (x : A) :
    ‖sourceOriginalRootCenteredSlot434 left right sentinel h a x‖=1 := by
  unfold sourceOriginalRootCenteredSlot434
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro e he
  split_ifs <;> simp [norm_mul,source_original_root_SIGN_NORM434]

theorem source_original_root_CENTERED_SLOT_INACTIVE434
    (left right : E → Addr) (sentinel : Addr → A)
    (h : E → A → Bool) (a : Addr) :
    sourceOriginalRootCenteredSlot434 left right sentinel h a (sentinel a)=1 := by
  unfold sourceOriginalRootCenteredSlot434
  apply Finset.prod_eq_one
  intro e he
  simp only [source_original_root_SIGN_SQUARE434,ite_self,one_mul]

theorem source_original_root_CENTERED_SLOT_UNMARKED434
    (left right : E → Addr) (sentinel : Addr → A)
    (h : E → A → Bool) (a : Addr) (x : A)
    (hl : ∀ e,left e≠a) (hr : ∀ e,right e≠a) :
    sourceOriginalRootCenteredSlot434 left right sentinel h a x=1 := by
  unfold sourceOriginalRootCenteredSlot434
  apply Finset.prod_eq_one
  intro e he
  rw [if_neg (hl e),if_neg (hr e),one_mul]

theorem source_original_root_CENTERED_SLOT_PRODUCT434
    (left right : E → Addr) (sentinel value : Addr → A) (h : E → A → Bool) :
    (∏ a : Addr,sourceOriginalRootCenteredSlot434 left right sentinel h a (value a)) =
    ∏ e : E,
      (sourceOriginalRootSign434 (h e (value (left e))) *
        sourceOriginalRootSign434 (h e (sentinel (left e)))) *
      (sourceOriginalRootSign434 (h e (value (right e))) *
        sourceOriginalRootSign434 (h e (sentinel (right e)))) := by
  unfold sourceOriginalRootCenteredSlot434
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro e he
  rw [Finset.prod_mul_distrib]
  have hs (a0 : Addr) :
      (∏ a : Addr,if a0=a then
        sourceOriginalRootSign434 (h e (value a)) *
          sourceOriginalRootSign434 (h e (sentinel a)) else 1) =
        sourceOriginalRootSign434 (h e (value a0)) *
          sourceOriginalRootSign434 (h e (sentinel a0)) := by
    rw [Finset.prod_eq_single_of_mem a0 (Finset.mem_univ _)]
    · simp
    · intro a ha hne
      exact if_neg (Ne.symm hne)
  rw [hs,hs]

/-- Finite edge equality product as centered address phases. The random
centering scalar is retained INSIDE the expectation. -/
theorem source_original_root_CENTERED_SLOT_AVERAGE434
    (left right : E → Addr) (sentinel value : Addr → A) :
    (∑ h : E → A → Bool,
      (∏ e : E,sourceOriginalRootSign434 (h e (sentinel (left e))) *
        sourceOriginalRootSign434 (h e (sentinel (right e)))) *
      (∏ a : Addr,sourceOriginalRootCenteredSlot434 left right sentinel h a (value a))) /
      (Fintype.card (E → A → Bool):ℂ) =
      ∏ e : E,if value (left e)=value (right e) then (1:ℂ) else 0 := by
  simp_rw [source_original_root_CENTERED_SLOT_PRODUCT434]
  exact source_original_root_INDEPENDENT_CENTERED_EQUALITIES434
    (fun e => value (left e)) (fun e => value (right e))
    (fun e => sentinel (left e)) (fun e => sentinel (right e))

/-- Potential owners, not path-dependent performed visits. -/
theorem source_original_root_INCIDENT_OWNER_COUNT434
    {Owner : Type} [DecidableEq Owner] (owner : Addr → Owner) (left right : E → Addr) :
    (((Finset.univ : Finset E).image (fun e => owner (left e))) ∪
      ((Finset.univ : Finset E).image (fun e => owner (right e)))).card ≤
      2*Fintype.card E := by
  apply (Finset.card_union_le _ _).trans
  have hl := Finset.card_image_le (s := (Finset.univ : Finset E)) (f := fun e => owner (left e))
  have hr := Finset.card_image_le (s := (Finset.univ : Finset E)) (f := fun e => owner (right e))
  simp only [Finset.card_univ] at hl hr
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestListedChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Literal original OLD-projected symmetric chain with one final global
LIST gate. Every local birth LIST gate is retained. All online seen-disjointness
tests are erased, and the actual numeric register is appended chronologically.
No padding, independent-residue process or canonical representative is used. -/
def sourceOriginalForestListedGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) → (Output → ℂ) → Output → List ℕ → ℂ
  | 0,start,F => fun Y H =>
      sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N start Vs V mu H
        (fun out H' => if H'.Nodup then F out else 0) Y
  | n+1,start,F => fun Y H =>
      sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N start Vs V mu H
        (fun yg hg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
          sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k hg
            (fun out ht => if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalForestListedGEChain434 q rho Vs V mu K zeta theta k N T
                n (start+1) F out ht else 0) yg
        else 0) Y

/-- Exact elimination of all numerical seen tests in the ACTUAL symmetric
projected source chain. It holds for every prior list, including repetitions,
and every physical output, including zero-mass fibres. -/
theorem source_original_forest_LISTED_CHAIN_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (n start : ℕ) (F : Output → ℂ) (Y : Output) (H : List ℕ) :
    sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F Y H =
    if H.Nodup then
      sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start (fun out _ => F out) Y H.toFinset
    else 0 := by
  induction n generalizing start Y H with
  | zero =>
      exact source_original_forest_LISTED_G_EXACT434 SP sm BP bm J ell cap
        q rho N start Vs V mu H (fun out _ => F out) Y
  | succ n ih =>
      let C := sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) (fun out _ => F out)
      let K' := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
      let C' := fun (out : Output) (s : Finset ℕ) =>
        if (∑ g : BG,(out.2 g).2.card) ≤ T then C out s else 0
      have hE (yg : Output) (hg : List ℕ) :
          (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k hg
              (fun out ht => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
                  q rho Vs V mu K zeta theta k N T n (start+1) F out ht else 0) yg
          else 0) =
          if hg.Nodup then
            (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
              physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
                q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k yg hg.toFinset C'
            else 0)
          else 0 := by
        by_cases hold : (∑ g : BG,(yg.2 g).2.card) ≤ T
        · simp only [if_pos hold]
          have heq :
              (fun (out : Output) (ht : List ℕ) =>
                if (∑ g : BG,(out.2 g).2.card) ≤ T then
                  sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
                    q rho Vs V mu K zeta theta k N T n (start+1) F out ht else 0) =
              (fun out ht => if ht.Nodup then C' out ht.toFinset else 0) := by
            funext out ht
            rw [ih]
            dsimp only [C',C]
            split_ifs <;> rfl
          rw [heq]
          exact source_original_forest_LISTED_E_EXACT434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k hg C' yg
        · simp [hold]
      simp only [sourceOriginalForestListedGEChain434,sourceOriginalOLDProjectedMemoryGEChain434]
      change sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N start Vs V mu H _ Y = _
      calc
        _ = sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N start Vs V mu H
            (fun yg hg => if hg.Nodup then
              (if (∑ g : BG,(yg.2 g).2.card) ≤ T then
                physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
                  q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k yg hg.toFinset C'
              else 0) else 0) Y := by
          apply congrArg (fun f : Output → List ℕ → ℂ =>
            sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N start Vs V mu H f Y)
          funext yg hg
          exact hE yg hg
        _ = _ := source_original_forest_LISTED_G_EXACT434 SP sm BP bm J ell cap
          q rho N start Vs V mu H
          (fun yg sg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
              q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k yg sg C' else 0) Y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestListedRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The literal coherent root in chronological-list form. In particular,
the initial BIG active list is not empty and is not forgotten. -/
def sourceOriginalForestListedRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N:ℂ)*
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y:ℂ)*
      star (physicalVacuum SP sm BP bm J ell y)*
      sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T N 0
        (physicalVacuum SP sm BP bm J ell) y
        (physicalOutputInitialBirths SP sm BP bm J ell y)

/-- Exact identification with the EXISTING projected original root.
No analytic estimate, reachability premise, prime injectivity, or phase
invariance of a canonical representative is assumed. This identity is
not a root-smallness statement. -/
theorem source_original_forest_LISTED_ROOT_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalForestListedRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  unfold sourceOriginalForestListedRoot434 sourceOriginalOLDProjectedMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [source_original_forest_LISTED_CHAIN_EXACT434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceShiftTwoPGroupLiteralBand -/

section

set_option maxHeartbeats 6000000
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Exactly the closed source P band [exp(t),exp(6t/5)],
including the natural left endpoint when it is prime. -/
noncomputable def sourceOriginalClosedPGroup (t : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊Real.exp ((6/5:ℝ)*t)⌋₊).filter
    (fun p => p.Prime ∧ Real.exp t ≤ (p:ℝ))

theorem source_original_P_closed_prime (t : ℝ) (p : ℕ)
    (hp : p ∈ sourceOriginalClosedPGroup t) :
    p.Prime := (Finset.mem_filter.mp hp).2.1

theorem source_original_P_closed_range (t : ℝ) (p : ℕ)
    (hp : p ∈ sourceOriginalClosedPGroup t) :
    Real.exp t ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp ((6/5:ℝ)*t) := by
  unfold sourceOriginalClosedPGroup at hp
  have hh := Finset.mem_filter.mp hp
  constructor
  · exact hh.2.2
  · exact (Nat.floor_le (Real.exp_nonneg _)).trans'
      (by exact_mod_cast (Finset.mem_Icc.mp hh.1).2)

theorem source_original_P_short_band_subset
    (t u v : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hv : v ≤ 6/5)
    (huv : u ≤ v) :
    sourcePrimeLogBand t u v ⊆ sourceOriginalClosedPGroup t := by
  intro p hp
  have hh := Finset.mem_filter.mp hp
  have hpr : p.Prime := hh.2
  have hI : p ∈ Finset.Ioc ⌊Real.exp (u*t)⌋₊
    ⌊Real.exp (v*t)⌋₊ := hh.1
  have hlowN : ⌊Real.exp (u*t)⌋₊ < p :=
    (Finset.mem_Ioc.mp hI).1
  have hhiN : p ≤ ⌊Real.exp (v*t)⌋₊ :=
    (Finset.mem_Ioc.mp hI).2
  have hLower : Real.exp (u*t) < (p:ℝ) := by
    have htFloor := Nat.lt_floor_add_one (Real.exp (u*t))
    have hSucc : (⌊Real.exp (u*t)⌋₊:ℝ)+1 ≤ p := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlowN)
    linarith
  have hUpper : p ≤ ⌊Real.exp ((6/5:ℝ)*t)⌋₊ := by
    have hExp : Real.exp (v*t) ≤ Real.exp ((6/5:ℝ)*t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hhiN.trans (Nat.floor_mono hExp)
  have hLower0 : Real.exp t ≤ (p:ℝ) :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hLower.le
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le p,hUpper⟩,
      hpr,hLower0⟩

theorem source_original_P_two_halves_disjoint (t : ℝ) :
    Disjoint (sourcePrimeLogBand t 1 (11/10))
      (sourcePrimeLogBand t (11/10) (6/5)) := by
  apply Finset.disjoint_left.mpr
  intro p hpA hpB
  have ha := (Finset.mem_Ioc.mp
    (Finset.mem_filter.mp hpA).1).2
  have hb := (Finset.mem_Ioc.mp
    (Finset.mem_filter.mp hpB).1).1
  omega

theorem source_original_P_closed_prime_ge_three
    (t : ℝ) (ht : 2 ≤ t) (p : ℕ)
    (hp : p ∈ sourceOriginalClosedPGroup t) : 3 ≤ p := by
  have hRange := (source_original_P_closed_range t p hp).1
  have he := Real.add_one_le_exp t
  have h3 : (3:ℝ) ≤ p := by linarith
  exact_mod_cast h3

theorem source_original_P_closed_quadratic_range
    (t : ℝ) (ht : 2 ≤ t) (p : ℕ)
    (hp : p ∈ sourceOriginalClosedPGroup t) :
    Real.exp ((3/4:ℝ)*t) < (p:ℝ) ∧
      (p:ℝ) ≤ (Real.exp ((3/4:ℝ)*t))^2 := by
  have hr := source_original_P_closed_range t p hp
  have hLower : Real.exp ((3/4:ℝ)*t) < Real.exp t :=
    Real.exp_lt_exp.mpr (by nlinarith)
  have hUpper : Real.exp ((6/5:ℝ)*t) ≤
      Real.exp ((3/2:ℝ)*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hSq : (Real.exp ((3/4:ℝ)*t))^2 =
      Real.exp ((3/2:ℝ)*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  constructor
  · exact hLower.trans_le hr.1
  · exact (hr.2.trans hUpper).trans_eq hSq.symm

end Green64Analytic.SourceBlockSieve

end

/-! ## SourcePActualAllGroupBands -/

section

set_option maxHeartbeats 2000000
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- The actual P_g prime sets from the two source logarithmic bands. -/
noncomputable def sourceOriginalPAllActualBands
    (r₀ : ℕ) (L : ℝ) :
    sourceOriginalPAllGroupType r₀ L → Finset ℕ :=
  fun g => sourceOriginalClosedPGroup
    ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val)

/-- Every true P_g lower endpoint lies at least at L^(1/10). -/
theorem source_original_P_all_actual_band_lower
    (r₀ : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (g : sourceOriginalPAllGroupType r₀ L) :
    L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val := by
  have hi : sourceOriginalPGroupIndex r₀ L g.val :=
    (Finset.mem_filter.mp g.property).2
  rcases hi with h | h
  · exact h.1
  · exact (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)).trans h.1

/-- The upper endpoint of every actual P_g is ≤ L^(2/5). -/
theorem source_original_P_all_actual_band_upper
    (r₀ : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (g : sourceOriginalPAllGroupType r₀ L) :
    (6/5:ℝ) * ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) ≤
      L^(2/5:ℝ) := by
  have hi : sourceOriginalPGroupIndex r₀ L g.val :=
    (Finset.mem_filter.mp g.property).2
  have heq : (6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) =
      (9/5:ℝ)*sourceOriginalPGroupScale r₀ L g.val := by ring
  rw [heq]
  rcases hi with h | h
  · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  · exact h.2

theorem source_original_P_all_actual_band_prime
    (r₀ : ℕ) (L : ℝ) :
    ∀ g p, p ∈ sourceOriginalPAllActualBands r₀ L g → p.Prime := by
  intro g p hp
  exact source_original_P_closed_prime _ p hp

theorem source_original_P_all_actual_band_log
    (r₀ : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∀ g p, p ∈ sourceOriginalPAllActualBands r₀ L g →
      Real.log (p:ℝ) ≤ L^(2/5:ℝ) := by
  intro g p hp
  have hPrime := source_original_P_all_actual_band_prime r₀ L g p hp
  have hpPos : (0:ℝ) < p := by
    exact_mod_cast hPrime.pos
  have hUpper := (source_original_P_closed_range _ p hp).2
  have hLog : Real.log (p:ℝ) ≤
      (6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) :=
    (Real.log_le_iff_le_exp hpPos).2 hUpper
  exact hLog.trans (source_original_P_all_actual_band_upper r₀ L hL g)

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceNativeOriginalMassUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The genuine reciprocal sum in every original moving P group is at most
four. This is exactly the elementary upper-bound argument of
SourcePActualAllLocal, separated from its unused Euler-weight assertions. -/
theorem source_original_P_all_actual_reciprocal_le_four434 (r : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ g : sourceOriginalPAllGroupType r L,
        (∑ p ∈ sourceOriginalPAllActualBands r L g, (p : ℝ)⁻¹) ≤ 4 := by
  have hPow : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hLarge : ∀ᶠ L : ℝ in atTop, 5 ≤ L^(1/10:ℝ) :=
    hPow.eventually (eventually_ge_atTop 5)
  filter_upwards [eventually_ge_atTop (1:ℝ), hLarge] with L hL hLargeL
  intro g
  let t : ℝ := (3/2:ℝ)*sourceOriginalPGroupScale r L g.val
  let w : ℝ := Real.exp ((3/4:ℝ)*t)
  have ht5 : 5 ≤ t :=
    hLargeL.trans (source_original_P_all_actual_band_lower r L hL g)
  have ht2 : 2 ≤ t := by linarith
  have hw : 1 < w := by
    dsimp [w]
    have he := Real.add_one_le_exp ((3/4:ℝ)*t)
    nlinarith
  have hPrime : ∀ p ∈ sourceOriginalClosedPGroup t, p.Prime :=
    fun p hp => source_original_P_closed_prime t p hp
  have hBand : ∀ p ∈ sourceOriginalClosedPGroup t,
      w < (p:ℝ) ∧ (p:ℝ) ≤ w^2 :=
    fun p hp => source_original_P_closed_quadratic_range t ht2 p hp
  change (∑ p ∈ sourceOriginalClosedPGroup t, (p:ℝ)⁻¹) ≤ 4
  exact source_quadratic_prime_reciprocal_le_four w
    (sourceOriginalClosedPGroup t) hw
    (fun p hp => ⟨hPrime p hp, (hBand p hp).1, (hBand p hp).2⟩)
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceNativeOriginalSmallReindex -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The complete original SMALL index type. -/
abbrev sourceNativeOriginalSmallType434 (r : ℕ) (L : ℝ) : Type :=
  {j : ℕ // j ∈ sourceNativeOriginalSmallIndices434 r L}

/-- The distinguished source index is the MINIMUM of the full SMALL family. -/
def sourceNativeOriginalSIndex434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) : ℕ :=
  (sourceNativeOriginalSmallIndices434 r L).min' hS

/-- Every remaining original SMALL index, independently of the BIG type. -/
abbrev sourceNativeOriginalTsType434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) : Type :=
  {j : ℕ // j ∈ (sourceNativeOriginalSmallIndices434 r L).erase
    (sourceNativeOriginalSIndex434 r L hS)}

theorem source_native_original_s_index_min434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    sourceNativeOriginalSIndex434 r L hS ∈ sourceNativeOriginalSmallIndices434 r L ∧
    ∀ j ∈ sourceNativeOriginalSmallIndices434 r L,
      sourceNativeOriginalSIndex434 r L hS ≤ j := by
  refine ⟨Finset.min'_mem _ _, ?_⟩
  intro j hj
  exact Finset.min'_le _ _ hj

theorem source_native_original_s_before_ts434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (i : sourceNativeOriginalTsType434 r L hS) :
    sourceNativeOriginalSIndex434 r L hS < i.val := by
  have hi := Finset.mem_erase.mp i.property
  have hle := (source_native_original_s_index_min434 r L hS).2 i.val hi.2
  omega

/-- The source Option carrier is exactly the full SMALL family: none is S. -/
def sourceNativeOriginalSmallOptionEquiv434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    Option (sourceNativeOriginalTsType434 r L hS) ≃
      sourceNativeOriginalSmallType434 r L where
  toFun
    | none => ⟨sourceNativeOriginalSIndex434 r L hS,
        (source_native_original_s_index_min434 r L hS).1⟩
    | some i => ⟨i.val, (Finset.mem_erase.mp i.property).2⟩
  invFun j := if hj : j.val = sourceNativeOriginalSIndex434 r L hS then none
    else some ⟨j.val, Finset.mem_erase.mpr ⟨hj,j.property⟩⟩
  left_inv := by
    intro z
    cases z with
    | none => simp
    | some i =>
        have hi := (Finset.mem_erase.mp i.property).1
        simp [hi]
  right_inv := by
    intro j
    dsimp only
    split_ifs with hj
    · exact Subtype.ext hj.symm
    · rfl

/-- The literal embedding of a full SMALL index into the existing full family. -/
def sourceNativeOriginalSmallToAll434 (r : ℕ) (L : ℝ)
    (j : sourceNativeOriginalSmallType434 r L) : sourceOriginalPAllGroupType r L :=
  ⟨j.val, (Finset.mem_filter.mp j.property).1⟩

/-- The literal independent BIG embedding. -/
def sourceNativeOriginalBigToAll434 (r : ℕ) (L : ℝ)
    (j : sourceNativeOriginalBigType434 r L) : sourceOriginalPAllGroupType r L :=
  ⟨j.val, (Finset.mem_filter.mp j.property).1⟩

def sourceNativeOriginalSGroup434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    sourceOriginalPAllGroupType r L :=
  sourceNativeOriginalSmallToAll434 r L
    ⟨sourceNativeOriginalSIndex434 r L hS,
      (source_native_original_s_index_min434 r L hS).1⟩

def sourceNativeOriginalTsGroup434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (i : sourceNativeOriginalTsType434 r L hS) : sourceOriginalPAllGroupType r L :=
  sourceNativeOriginalSmallToAll434 r L
    ⟨i.val, (Finset.mem_erase.mp i.property).2⟩

/-- The independent full SMALL/BIG types give every original group once. -/
def sourceNativeOriginalSmallBigEquiv434
    (r : ℕ) (L : ℝ) (hL : 1 < L) :
    sourceNativeOriginalSmallType434 r L ⊕ sourceNativeOriginalBigType434 r L ≃
      sourceOriginalPAllGroupType r L where
  toFun
    | Sum.inl j => sourceNativeOriginalSmallToAll434 r L j
    | Sum.inr j => sourceNativeOriginalBigToAll434 r L j
  invFun j := if hs : j.val ∈ sourceNativeOriginalSmallIndices434 r L then
      Sum.inl ⟨j.val, hs⟩
    else Sum.inr ⟨j.val, by
      have hj : j.val ∈ sourceNativeOriginalSmallIndices434 r L ∪
          sourceNativeOriginalBigIndices434 r L := by
        rw [source_native_original_group_partition434]
        exact j.property
      exact (Finset.mem_union.mp hj).resolve_left hs⟩
  left_inv := by
    intro z
    cases z with
    | inl j =>
        have hj := j.property
        simp [sourceNativeOriginalSmallToAll434, hj]
    | inr j =>
        have hn : j.val ∉ sourceNativeOriginalSmallIndices434 r L := by
          intro hs
          exact Finset.disjoint_left.mp
            (source_native_original_group_partition_disjoint434 r L hL) hs j.property
        simp [sourceNativeOriginalBigToAll434, hn]
  right_inv := by
    intro j
    dsimp only
    split_ifs <;> rfl

/-- The full literal family in physical Option-SMALL plus independent BIG form. -/
def sourceNativeOriginalFullEquiv434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hL : 1 < L) :
    (Option (sourceNativeOriginalTsType434 r L hS) ⊕
      sourceNativeOriginalBigType434 r L) ≃ sourceOriginalPAllGroupType r L :=
  (Equiv.sumCongr (sourceNativeOriginalSmallOptionEquiv434 r L hS)
      (Equiv.refl (sourceNativeOriginalBigType434 r L))).trans
    (sourceNativeOriginalSmallBigEquiv434 r L hL)

/-- Explicit association from the C complete-group carrier to physical Option. -/
def sourceNativeOptionSumEquiv434 (ι β : Type) :
    Unit ⊕ (ι ⊕ β) ≃ (Option ι ⊕ β) where
  toFun
    | Sum.inl _ => Sum.inl none
    | Sum.inr (Sum.inl i) => Sum.inl (some i)
    | Sum.inr (Sum.inr j) => Sum.inr j
  invFun
    | Sum.inl none => Sum.inl ()
    | Sum.inl (some i) => Sum.inr (Sum.inl i)
    | Sum.inr j => Sum.inr (Sum.inr j)
  left_inv := by
    intro z
    rcases z with u | i | j
    · cases u
      rfl
    · rfl
    · rfl
  right_inv := by
    intro z
    rcases z with z | j
    · cases z <;> rfl
    · rfl

/-- The C carrier has exactly the same full original group family. -/
def sourceNativeOriginalCompleteEquiv434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hL : 1 < L) :
    (Unit ⊕ (sourceNativeOriginalTsType434 r L hS ⊕
      sourceNativeOriginalBigType434 r L)) ≃ sourceOriginalPAllGroupType r L :=
  (sourceNativeOptionSumEquiv434 _ _).trans
    (sourceNativeOriginalFullEquiv434 r L hS hL)

theorem source_native_original_full_equiv_none434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L) :
    sourceNativeOriginalFullEquiv434 r L hS hL (Sum.inl none) =
      sourceNativeOriginalSGroup434 r L hS := rfl

theorem source_native_original_full_equiv_some434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (i : sourceNativeOriginalTsType434 r L hS) :
    sourceNativeOriginalFullEquiv434 r L hS hL (Sum.inl (some i)) =
      sourceNativeOriginalTsGroup434 r L hS i := rfl

theorem source_native_original_full_equiv_big434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (j : sourceNativeOriginalBigType434 r L) :
    sourceNativeOriginalFullEquiv434 r L hS hL (Sum.inr j) =
      sourceNativeOriginalBigToAll434 r L j := rfl

/-- Removing exactly S reduces only the SMALL count by exactly one. -/
theorem source_native_original_ts_card434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    Fintype.card (sourceNativeOriginalTsType434 r L hS) =
      (sourceNativeOriginalSmallIndices434 r L).card-1 ∧
    Fintype.card (sourceNativeOriginalTsType434 r L hS)+1 =
      (sourceNativeOriginalSmallIndices434 r L).card := by
  have hmem := (source_native_original_s_index_min434 r L hS).1
  have hc : Fintype.card (sourceNativeOriginalTsType434 r L hS) =
      (sourceNativeOriginalSmallIndices434 r L).card-1 := by
    simpa only [Fintype.card_coe] using Finset.card_erase_of_mem hmem
  have hp : 0 < (sourceNativeOriginalSmallIndices434 r L).card := Finset.card_pos.mpr hS
  exact ⟨hc, by omega⟩

/-- The true remaining SMALL family still has logarithmically many groups.
The nonempty/minimum choice and threshold precede all later comparison parameters. -/
theorem eventually_source_native_original_small_reindex434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 r L).Nonempty ∧
      ∀ hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty,
        Real.log L/(80*Real.log 2) ≤
          (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) := by
  filter_upwards [eventually_source_native_original_group_counts434 r hr,
    eventually_ge_atTop (Real.exp (80*Real.log 2)),
    eventually_ge_atTop (2:ℝ)] with L hcounts hloglarge hL
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h40 : 0 < 40*Real.log 2 := mul_pos (by norm_num) h2
  have hlog : 80*Real.log 2 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos _) hloglarge
    simpa only [Real.log_exp] using h
  have htwoReal : (2:ℝ) ≤ (sourceNativeOriginalSmallIndices434 r L).card := by
    apply le_trans _ hcounts.1
    apply (le_div_iff₀ h40).mpr
    nlinarith
  have htwo : 2 ≤ (sourceNativeOriginalSmallIndices434 r L).card := by
    exact_mod_cast htwoReal
  refine ⟨by linarith, Finset.card_pos.mp (by omega), ?_⟩
  intro hS
  have hc := (source_native_original_ts_card434 r L hS).2
  have hhalf : (sourceNativeOriginalSmallIndices434 r L).card ≤
      2*Fintype.card (sourceNativeOriginalTsType434 r L hS) := by omega
  have hhalfReal : ((sourceNativeOriginalSmallIndices434 r L).card:ℝ) ≤
      2*(Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) := by
    exact_mod_cast hhalf
  have hdiv : Real.log L/(80*Real.log 2) =
      (Real.log L/(40*Real.log 2))/2 := by
    rw [div_div]
    congr 1
    ring
  rw [hdiv]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  exact hcounts.1.trans (by nlinarith)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourcePActualAllDisjoint -/

section

set_option maxHeartbeats 2000000
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- The original dyadic scale drops by at least a factor two
between any two distinct ordered source P indices. -/
theorem source_original_P_actual_scale_dyadic_separation
    (r₀ j k : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 < L)
    (hjk : j < k) :
    2 * sourceOriginalPGroupScale r₀ L k ≤
      sourceOriginalPGroupScale r₀ L j := by
  let d : ℝ := (r₀:ℝ)*(11/5:ℝ)
  let a : ℝ := (2:ℝ)^j
  let b : ℝ := (2:ℝ)^k
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hd : 0 < d := by dsimp [d]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : 2*a ≤ b := by
    dsimp [a,b]
    have hh : (2:ℝ)^(j+1) ≤ (2:ℝ)^k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ] at hh
    nlinarith
  have hnum : (2*L)*(d*a) ≤ L*(d*b) := by
    have hh := mul_le_mul_of_nonneg_left hab (le_of_lt (mul_pos hL hd))
    nlinarith
  have hdena : 0 < d*a := mul_pos hd ha
  have hdenb : 0 < d*b := mul_pos hd hb
  have hdiv : (2*L)/(d*b) ≤ L/(d*a) :=
    (div_le_div_iff₀ hdenb hdena).mpr hnum
  dsimp [sourceOriginalPGroupScale, d, a, b] at hdiv ⊢
  calc
    2 * (L / ((r₀:ℝ)*(11/5:ℝ)*(2:ℝ)^k)) =
        (2*L)/((r₀:ℝ)*(11/5:ℝ)*(2:ℝ)^k) := by ring
    _ ≤ _ := by simpa [mul_assoc] using hdiv
/-- Actual source P bands for distinct dyadic indices are disjoint,
with exact inclusive endpoint semantics from the original closed bands. -/
theorem source_original_P_actual_all_disjoint
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 < L) :
    ∀ g h : sourceOriginalPAllGroupType r₀ L,
      ∀ p, p ∈ sourceOriginalPAllActualBands r₀ L g →
        p ∈ sourceOriginalPAllActualBands r₀ L h → g = h := by
  intro g h p hpg hph
  classical
  by_contra hne
  have hval : g.val ≠ h.val := by
    intro hv
    exact hne (Subtype.ext hv)
  rcases lt_or_gt_of_ne hval with hjk | hkj
  · have hs := source_original_P_actual_scale_dyadic_separation
      r₀ g.val h.val L hr₀ hL hjk
    have hgPos : 0 < sourceOriginalPGroupScale r₀ L g.val := by
      unfold sourceOriginalPGroupScale
      have hr : (0:ℝ) < r₀ := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
      positivity
    have hgap : (6/5:ℝ) *
        ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L h.val) <
        (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val := by
      nlinarith
    have he := Real.exp_strictMono hgap
    have hRg := source_original_P_closed_range
      ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) p hpg
    have hRh := source_original_P_closed_range
      ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L h.val) p hph
    linarith
  · have hs := source_original_P_actual_scale_dyadic_separation
      r₀ h.val g.val L hr₀ hL hkj
    have hhPos : 0 < sourceOriginalPGroupScale r₀ L h.val := by
      unfold sourceOriginalPGroupScale
      have hr : (0:ℝ) < r₀ := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
      positivity
    have hgap : (6/5:ℝ) *
        ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) <
        (3/2:ℝ)*sourceOriginalPGroupScale r₀ L h.val := by
      nlinarith
    have he := Real.exp_strictMono hgap
    have hRg := source_original_P_closed_range
      ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val) p hpg
    have hRh := source_original_P_closed_range
      ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L h.val) p hph
    linarith

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceNativeOriginalSmallGroups -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The actual original prime band at the minimum full SMALL index. -/
def sourceNativeOriginalS434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) : Finset ℕ :=
  sourceOriginalPAllActualBands r L (sourceNativeOriginalSGroup434 r L hS)

/-- Every other actual original SMALL prime band. -/
def sourceNativeOriginalTs434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (i : sourceNativeOriginalTsType434 r L hS) : Finset ℕ :=
  sourceOriginalPAllActualBands r L (sourceNativeOriginalTsGroup434 r L hS i)

/-- Every original BIG prime band on its own existing index type. -/
def sourceNativeOriginalTb434 (r : ℕ) (L : ℝ)
    (j : sourceNativeOriginalBigType434 r L) : Finset ℕ :=
  sourceOriginalPAllActualBands r L (sourceNativeOriginalBigToAll434 r L j)

/-- The literal union of all original P groups. -/
def sourceNativeOriginalG434 (r : ℕ) (L : ℝ) : Finset ℕ :=
  Finset.univ.biUnion (sourceOriginalPAllActualBands r L)

/-- Exact family equality in the C complete-group carrier. -/
theorem source_native_original_complete_family434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L) :
    Sum.elim (fun _ : Unit => sourceNativeOriginalS434 r L hS)
      (Sum.elim (sourceNativeOriginalTs434 r L hS) (sourceNativeOriginalTb434 r L)) =
    fun g => sourceOriginalPAllActualBands r L
      (sourceNativeOriginalCompleteEquiv434 r L hS hL g) := by
  funext g
  rcases g with u | i | j
  · cases u
    rfl
  · rfl
  · rfl

/-- Exact family equality in the physical Option-SMALL carrier. -/
theorem source_native_original_option_small_family434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L) :
    (fun g : Option (sourceNativeOriginalTsType434 r L hS) =>
      match g with
      | none => sourceNativeOriginalS434 r L hS
      | some i => sourceNativeOriginalTs434 r L hS i) =
    fun g => sourceOriginalPAllActualBands r L
      (sourceNativeOriginalFullEquiv434 r L hS hL (Sum.inl g)) := by
  funext g
  cases g <;> rfl

/-- Reindexing preserves the full prime union, with no removal of any group. -/
theorem source_native_original_union_reindex434
    {ι β : Type} [Fintype ι] [Fintype β]
    (e : ι ≃ β) (P : β → Finset ℕ) :
    Finset.univ.biUnion (fun i => P (e i)) = Finset.univ.biUnion P := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩

/-- The literal G field of the native comparison record, using the complete
original prime union and precisely S, all remaining Ts, and all independent Tb. -/
theorem source_native_original_G_identity434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L) :
    sourceNativeOriginalG434 r L =
      sourceNativeOriginalS434 r L hS ∪
        Finset.univ.biUnion (sourceNativeOriginalTs434 r L hS) ∪
        Finset.univ.biUnion (sourceNativeOriginalTb434 r L) := by
  have he := source_native_original_union_reindex434
    (sourceNativeOriginalFullEquiv434 r L hS hL)
    (sourceOriginalPAllActualBands r L)
  unfold sourceNativeOriginalG434
  rw [←he]
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨g, hg⟩
    rcases g with g | j
    · cases g with
      | none => exact Or.inl (Or.inl hg)
      | some i => exact Or.inl (Or.inr ⟨i,hg⟩)
    · exact Or.inr ⟨j,hg⟩
  · rintro ((hs | ⟨i,hi⟩) | ⟨j,hj⟩)
    · exact ⟨Sum.inl none, hs⟩
    · exact ⟨Sum.inl (some i), hi⟩
    · exact ⟨Sum.inr j, hj⟩

/-- An arbitrary commutative finite product is preserved by the exact group
bijection. This is a product identity, not a claim about an unimported weight. -/
theorem source_native_original_full_product434
    {M : Type} [CommMonoid M]
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (F : sourceOriginalPAllGroupType r L → M) :
    (∏ g, F g) = F (sourceNativeOriginalSGroup434 r L hS) *
      (∏ i : sourceNativeOriginalTsType434 r L hS,
        F (sourceNativeOriginalTsGroup434 r L hS i)) *
      (∏ j : sourceNativeOriginalBigType434 r L,
        F (sourceNativeOriginalBigToAll434 r L j)) := by
  simpa only [Fintype.prod_sum_type, Fintype.prod_option,
    source_native_original_full_equiv_none434,
    source_native_original_full_equiv_some434,
    source_native_original_full_equiv_big434] using
    ((sourceNativeOriginalFullEquiv434 r L hS hL).prod_comp F).symm

/-- The original actual prime-band family admits the same exact product split. -/
theorem source_native_original_band_product434
    {M : Type} [CommMonoid M]
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L)
    (F : Finset ℕ → M) :
    (∏ g : sourceOriginalPAllGroupType r L, F (sourceOriginalPAllActualBands r L g)) =
      F (sourceNativeOriginalS434 r L hS) *
      (∏ i : sourceNativeOriginalTsType434 r L hS, F (sourceNativeOriginalTs434 r L hS i)) *
      (∏ j : sourceNativeOriginalBigType434 r L, F (sourceNativeOriginalTb434 r L j)) :=
  source_native_original_full_product434 r L hS hL
    (fun g => F (sourceOriginalPAllActualBands r L g))

/-- Complete-family cardinality, with separate SMALL and BIG counts. -/
theorem source_native_original_all_card434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1 < L) :
    (sourceOriginalPAllGroupIndices r L).card =
      (Fintype.card (sourceNativeOriginalTsType434 r L hS)+1) +
        Fintype.card (sourceNativeOriginalBigType434 r L) := by
  simpa only [Fintype.card_sum, Fintype.card_option, Fintype.card_coe] using
    (Fintype.card_congr (sourceNativeOriginalFullEquiv434 r L hS hL)).symm

/-- All source prime disjointness survives the exact original-family split. -/
theorem source_native_original_small_group_disjoint434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hr : 1 ≤ r) (hL : 1 < L) :
    (∀ i, Disjoint (sourceNativeOriginalS434 r L hS)
      (sourceNativeOriginalTs434 r L hS i)) ∧
    (∀ j, Disjoint (sourceNativeOriginalS434 r L hS)
      (sourceNativeOriginalTb434 r L j)) ∧
    (Pairwise (fun i j => Disjoint (sourceNativeOriginalTs434 r L hS i)
      (sourceNativeOriginalTs434 r L hS j))) ∧
    (Pairwise (fun i j => Disjoint (sourceNativeOriginalTb434 r L i)
      (sourceNativeOriginalTb434 r L j))) ∧
    (∀ i j, Disjoint (sourceNativeOriginalTs434 r L hS i)
      (sourceNativeOriginalTb434 r L j)) := by
  have hp : ∀ g h : sourceOriginalPAllGroupType r L, g ≠ h →
      Disjoint (sourceOriginalPAllActualBands r L g)
        (sourceOriginalPAllActualBands r L h) := by
    intro g h hne
    apply Finset.disjoint_left.mpr
    intro p hpg hph
    exact hne (source_original_P_actual_all_disjoint r L hr
      (zero_lt_one.trans hL) g h p hpg hph)
  have hsb := source_native_original_group_partition_disjoint434 r L hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hp
    intro he
    have hv : sourceNativeOriginalSIndex434 r L hS = i.val :=
      congrArg Subtype.val he
    have hlt := source_native_original_s_before_ts434 r L hS i
    omega
  · intro j
    apply hp
    intro he
    have hv : sourceNativeOriginalSIndex434 r L hS = j.val :=
      congrArg Subtype.val he
    have hs := (source_native_original_s_index_min434 r L hS).1
    rw [hv] at hs
    exact Finset.disjoint_left.mp hsb hs j.property
  · intro i j hij
    apply hp
    intro he
    apply hij
    have hv : i.val = j.val :=
      congrArg (fun g : sourceOriginalPAllGroupType r L => g.val) he
    exact Subtype.ext hv
  · intro i j hij
    apply hp
    intro he
    apply hij
    have hv : i.val = j.val :=
      congrArg (fun g : sourceOriginalPAllGroupType r L => g.val) he
    exact Subtype.ext hv
  · intro i j
    apply hp
    intro he
    have hv : i.val = j.val := congrArg Subtype.val he
    have hi := (Finset.mem_erase.mp i.property).2
    rw [hv] at hi
    exact Finset.disjoint_left.mp hsb hi j.property
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalSmallBounds -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The physical Option-SMALL carrier has exactly the full original SMALL count. -/
theorem source_native_original_option_card434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    Fintype.card (Option (sourceNativeOriginalTsType434 r L hS)) =
      (sourceNativeOriginalSmallIndices434 r L).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (sourceNativeOriginalSmallOptionEquiv434 r L hS)

/-- Both actual SMALL carrier counts follow from the original full-family
count, with a single threshold before all later comparison parameters. -/
theorem eventually_source_native_original_small_counts434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 r L).Nonempty ∧
      ∀ hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty,
        Real.log L/(40*Real.log 2) ≤
          (Fintype.card (Option (sourceNativeOriginalTsType434 r L hS)):ℝ) ∧
        Real.log L/(80*Real.log 2) ≤
          (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) := by
  filter_upwards [eventually_source_native_original_small_reindex434 r hr,
    eventually_source_native_original_group_counts434 r hr] with L hsmall hcounts
  refine ⟨hsmall.1, hsmall.2.1, ?_⟩
  intro hS
  constructor
  · rw [source_native_original_option_card434]
    exact hcounts.1
  · exact hsmall.2.2 hS

/-- The minimum index is the largest SMALL scale; every remaining SMALL
scale is separated by the original dyadic factor of at least two. -/
theorem source_native_original_s_scale_order434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hr : 1 ≤ r) (hL : 0 < L)
    (i : sourceNativeOriginalTsType434 r L hS) :
    2*sourceOriginalPGroupScale r L i.val ≤
      sourceOriginalPGroupScale r L (sourceNativeOriginalSIndex434 r L hS) :=
  source_original_P_actual_scale_dyadic_separation
    r (sourceNativeOriginalSIndex434 r L hS) i.val L hr hL
    (source_native_original_s_before_ts434 r L hS i)

/-- In the actual closed source prime bands, every remaining SMALL prime is
strictly below every distinguished S prime. No band nonemptiness is assumed. -/
theorem source_native_original_s_prime_order434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (hr : 1 ≤ r) (hL : 0 < L)
    (i : sourceNativeOriginalTsType434 r L hS)
    (p s : ℕ) (hp : p ∈ sourceNativeOriginalTs434 r L hS i)
    (hs : s ∈ sourceNativeOriginalS434 r L hS) : p < s := by
  have hsep := source_native_original_s_scale_order434 r L hS hr hL i
  have hiPos : 0 < sourceOriginalPGroupScale r L i.val := by
    unfold sourceOriginalPGroupScale
    have hrPos : (0:ℝ) < r := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr)
    positivity
  have hgap : (6/5:ℝ)*((3/2:ℝ)*sourceOriginalPGroupScale r L i.val) <
      (3/2:ℝ)*sourceOriginalPGroupScale r L
        (sourceNativeOriginalSIndex434 r L hS) := by nlinarith
  have hpRange := source_original_P_closed_range
    ((3/2:ℝ)*sourceOriginalPGroupScale r L i.val) p hp
  have hsRange := source_original_P_closed_range
    ((3/2:ℝ)*sourceOriginalPGroupScale r L
      (sourceNativeOriginalSIndex434 r L hS)) s hs
  have hreal : (p:ℝ) < s :=
    hpRange.2.trans_lt ((Real.exp_strictMono hgap).trans_le hsRange.1)
  exact_mod_cast hreal
end Green64Analytic.SourceBlockSieve

end

end

