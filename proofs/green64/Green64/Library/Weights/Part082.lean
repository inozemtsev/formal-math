module

public import Green64.Library.Correlation.PhysicalFreeSlotMassBudget
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part081
public import Green64.Library.Weights.Part072
public import Green64.Library.Weights.Part055
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.ActualInitialVacuumFactor
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part080

@[expose] public section

/-!
# Weights / Part082

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalNTiltedMassEventual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Instantiate the TRUE source depth N(L)=2 ceil(L^0.52) and original
BIG prime minimum exp(L^c), using the already-proved eventual physical
visit-size theorem. Works uniformly for any finite group/prime alphabet,
original shared-copy pattern and all BIG source/target permutations. No
unproved normalization or arbitrary-L baseline positivity is smuggled in. -/
theorem eventually_source_original_B416_true_N_tilted_free_slot_budget434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
        (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
        (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
        (V : G → ℝ) (hV : ∀ g,V g=∑ p : BP g,1/(bm g p:ℝ))
        (hVpos : ∀ g,0 < V g)
        (hprime : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
        (J ell m : ℕ) (pat : SourcePattern G J m),
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,
          physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V g p) ≤
      (1+2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) /
        Real.exp (L^c))^((J+ell)*(Fintype.card G)) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc]
    with L hSize
  intro G iG dG BP fi di bm nz q hq hq1 V hV hVpos hprime J ell m pat
  have hs : ∀ g p, 2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) ≤
      (bm g p:ℝ) := by
    intro g p
    exact hSize (bm g p) (hprime g p)
  exact source_original_B415_tilted_free_slot_mass_budget434
    BP bm q hq hq1 (2*Nat.ceil (L^(0.52:ℝ)))
    V hV hVpos (Real.exp (L^c)) (Real.exp_pos _) hprime hs J ell m pat
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualDataTiltedMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Insert the *actual* SourceComparisonData434 prime alphabet, harmonic BIG
mass, physicalSourceMuTilde and depth N(L). The only extra assumptions are
the literal original BIG prime lower bound and harmonic Vbig identity, already
present in the source unfiltered physical consumer. No normalization of mu~. -/
theorem eventually_source_original_B417_actual_data_tilted_free_slot_bound434
    (cfg : SourceComparisonFixed434) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
        (x Y Hprime : ℝ)
        (d : SourceComparisonData434 ι G cfg x L Y Hprime)
        [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
        (hTbLower : ∀ g,∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
        (hVbig : ∀ g,d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
        (J ell m : ℕ) (pat : SourcePattern G J m),
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,
          physicalSourceMuTilde BP bm cfg.q0
            (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig g p) ≤
      (1+2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) /
        Real.exp (L^cfg.cexp))^((J+ell)*(Fintype.card G)) := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B416_true_N_tilted_free_slot_budget434
    cfg.cexp hc] with L hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig J ell m pat
  dsimp only
  let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  have hV : ∀ g,d.Vbig g = ∑ p : BP g, 1/(bm g p:ℝ) := by
    intro g
    calc
      d.Vbig g = ∑ p ∈ d.Tb g, (1:ℝ)/(p:ℝ) := hVbig g
      _ = ∑ p : BP g, 1/(bm g p:ℝ) := by
        simpa only [BP,bm] using
          (Finset.sum_coe_sort (d.Tb g)
            (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  have hv : ∀ g,0 < d.Vbig g :=
    fun g => cfg.hv.trans_le (d.hVbig g)
  have hp : ∀ g (p : BP g),Real.exp (L^cfg.cexp) ≤ (bm g p:ℝ) :=
    fun g p => hTbLower g p.val p.property
  exact hL BP bm cfg.q0 cfg.hq0.le cfg.hq1.le d.Vbig
    hV hv hp J ell m pat
end Green64Analytic.CorrelationSquare

end

end

/-! ## NearOneMassExponent -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A near-one physical BIG mass can be absorbed without ever replacing it
by 1. The exact n*epsilon budget is exposed to the source prime/group
parameter theorem, with no artificial counting measure. -/
theorem source_original_B418_near_one_free_slot_exp_budget434
    (epsilon : ℝ) (he : 0 ≤ epsilon) (n : ℕ)
    (hbudget : (n:ℝ)*epsilon ≤ 1) :
    (1+epsilon)^n ≤ Real.exp 1 := by
  have hbase : 0 ≤ 1+epsilon := by linarith only [he]
  have hexp : 1+epsilon ≤ Real.exp epsilon := by
    simpa only [add_comm] using Real.add_one_le_exp epsilon
  have hpow := pow_le_pow_left₀ hbase hexp n
  rw [← Real.exp_nat_mul] at hpow
  exact hpow.trans (Real.exp_le_exp.mpr hbudget)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceGroupTiltExponent -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The true BIG group count O(log L) and source depth 2 ceil(L^0.52) make
its exact tilted-law mass exponent eventually at most one. J and ell are
fixed BEFORE L; no arbitrary family/cardinality or scalar-cancellation
hypothesis is used. -/
theorem eventually_source_original_B419_tilted_group_exponent_le_one434
    (c C0 : ℝ) (hc : 0 < c) (hC0 : 0 ≤ C0) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G]
        (hGroups : (Fintype.card G : ℝ) ≤ C0 * Real.log L),
      (((J+ell)*(Fintype.card G):ℕ):ℝ) *
        (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) /
          Real.exp (L^c)) ≤ 1 := by
  let r : ℝ := 2 + ((J+ell:ℕ):ℝ)*C0
  have hr2 : 2 ≤ r := by
    dsimp [r]
    have hn : 0 ≤ ((J+ell:ℕ):ℝ)*C0 :=
      mul_nonneg (Nat.cast_nonneg _) hC0
    linarith only [hn]
  have hr : 0 ≤ r := by linarith only [hr2]
  obtain ⟨L0,hDom⟩ := source_original_circle_eventual_exp_dominance434
    c 2 1 hc (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop L0, eventually_ge_atTop r]
    with L hL0 hLr
  obtain ⟨hL4,hExpBound⟩ := hDom L hL0
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hLpos : 0 < L := by linarith only [hL4]
  have hExp : 4*L^2*r^2 ≤ Real.exp (L^c) := by
    simpa only [Real.rpow_two] using
      (hExpBound r hr (by simpa using hLr))
  intro G fi hGroups
  have hlog : Real.log L ≤ L := Real.log_le_self hLpos.le
  have hG : (Fintype.card G:ℝ) ≤ C0*L := by
    exact hGroups.trans (mul_le_mul_of_nonneg_left hlog hC0)
  have hNpow : L^(0.52:ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1
      (by norm_num : (0.52:ℝ) ≤ 1)
  have hceil : ((Nat.ceil (L^(0.52:ℝ))):ℝ) ≤ L^(0.52:ℝ)+1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hLpos.le (0.52:ℝ))).le
  have hN : (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)) ≤ 8*L := by
    push_cast
    linarith only [hNpow,hceil,hL4]
  have hNnonneg : 0 ≤ (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)) := by positivity
  have hn : 0 ≤ ((J+ell)*(Fintype.card G):ℕ) := Nat.zero_le _
  have hJ : 0 ≤ ((J+ell:ℕ):ℝ) := Nat.cast_nonneg _
  have hGroupMul := mul_le_mul_of_nonneg_left hG hJ
  have hnL : (((J+ell)*(Fintype.card G):ℕ):ℝ) ≤ r*L := by
    calc
      _ = ((J+ell:ℕ):ℝ)*(Fintype.card G:ℝ) := by push_cast; ring
      _ ≤ ((J+ell:ℕ):ℝ)*(C0*L) := hGroupMul
      _ ≤ r*L := by dsimp [r]; nlinarith only [hLpos]
  have hrL : 0 ≤ r*L := mul_nonneg hr hLpos.le
  have hmult : (((J+ell)*(Fintype.card G):ℕ):ℝ) *
      (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)) ≤
      (r*L)*(8*L) :=
    mul_le_mul hnL hN hNnonneg hrL
  have hrr : 2*r ≤ r^2 := by nlinarith only [hr2, sq_nonneg (r-2)]
  have hscale : 4*L^2*(2*r) ≤ 4*L^2*r^2 :=
    mul_le_mul_of_nonneg_left hrr (by positivity)
  have hnum : (((J+ell)*(Fintype.card G):ℕ):ℝ) *
      (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)) ≤
      Real.exp (L^c) := by
    calc
      _ ≤ (r*L)*(8*L) := hmult
      _ = 4*L^2*(2*r) := by ring
      _ ≤ 4*L^2*r^2 := hscale
      _ ≤ _ := hExp
  have hdiv : (((J+ell)*(Fintype.card G):ℕ):ℝ) *
       (2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)) /
        Real.exp (L^c) ≤ 1 :=
    (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa using hnum)
  convert hdiv using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualDataTiltedMassUniform -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The TRUE SourceComparisonData original BIG group-count cap absorbs all
non-normalized tilted free-slot costs as a fixed absolute constant exp(1).
The BIG source has its original depth N(L), prime alphabet and Fourier
parameter order: J and ell fixed before the final sufficiently-large L.
No assumption that physicalSourceMuTilde sums to one, no OLD/Fock counts. -/
theorem eventually_source_original_B420_actual_data_tilted_mass_uniform434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
        (x Y Hprime : ℝ)
        (d : SourceComparisonData434 ι G cfg x L Y Hprime)
        [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
        (hTbLower : ∀ g,∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
        (hVbig : ∀ g,d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
        (pat : SourcePattern G J m),
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,
          physicalSourceMuTilde BP bm cfg.q0
            (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig g p) ≤ Real.exp 1 := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B417_actual_data_tilted_free_slot_bound434 cfg,
    eventually_source_original_B419_tilted_group_exponent_le_one434
      cfg.cexp cfg.C0 hc cfg.hC0 J ell] with L hRaw hGroup
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig pat
  dsimp only
  have hBound := hRaw x Y Hprime d hTbLower hVbig J ell m pat
  let eps : ℝ := 2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) /
    Real.exp (L^cfg.cexp)
  have he : 0 ≤ eps := by dsimp [eps]; positivity
  have hProductBudget := hGroup (d.hBigGroups)
  have hAbsorb := source_original_B418_near_one_free_slot_exp_budget434
    eps he ((J+ell)*(Fintype.card G)) (by simpa only [eps] using hProductBudget)
  exact hBound.trans (by simpa only [eps] using hAbsorb)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SharpTiltedOrbitCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual original Fock/OLD/seen marked collision with the TRUE
non-normalized physical tilde law and the SHARP near-one free-slot mass,
not a normalized or artificially independent source. -/
theorem source_original_B421_sharp_physical_tilt_orbit_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (N : ℕ)
    (hsize : ∀ g (p : {p : ℕ // p ∈ P g}),
      2*((N+1:ℕ):ℝ) ≤ (p.val:ℝ))
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell)
      (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell cap sizes hsizes prime a t)) S) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm q N V)
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs V (physicalSourceMuTilde BP bm q N V) K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns (physicalSourceMuTilde BP bm q N V) V K q Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (1+2*((N+1:ℕ):ℝ)/Pmin)^((J+ell)*Fintype.card G) := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let mu := physicalSourceMuTilde BP bm q N V
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let C : ℝ :=
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG,memorySmallRowConstant q (Vs g) ell) * B
  have hVpos : ∀ g, 0 < V g := by
    intro g
    exact lt_of_lt_of_le hv (hVmin g)
  have hVsub : ∀ g, V g = ∑ p : BP g, 1/(bm g p:ℝ) := by
    intro g
    calc
      _ = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(bm g p:ℝ) := by
        simpa only [BP,bm] using
          (Finset.sum_coe_sort (P g) (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  have hpmin : ∀ g (p : BP g), Pmin ≤ (bm g p:ℝ) := by
    intro g p
    exact hPmin g p.val p.property
  have hmu_pos : ∀ g p, 0 < mu g p := by
    intro g p
    exact (source_original_B410_physical_mu_tilde_positive_bound434
      BP bm q hq.le hq1.le N V hVpos hsize g p).1
  have hmu : ∀ g p, 0 ≤ mu g p := by
    intro g p
    exact (hmu_pos g p).le
  have hMass :
    (∏ g : G,∏ i : Fin (J+ell),
      if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
      else ∑ p : BP g,mu g p) ≤
    (1+2*((N+1:ℕ):ℝ)/Pmin)^((J+ell)*Fintype.card G) := by
    exact source_original_B415_tilted_free_slot_mass_budget434
      BP bm q hq.le hq1.le N V hVsub hVpos Pmin hP hpmin hsize J ell m pat
  have hsqrt : Real.sqrt q < 1 := by
    have hsq := Real.sq_sqrt (le_of_lt hq)
    have hn := Real.sqrt_nonneg q
    nlinarith only [hsq,hn,hq1]
  have hden : 0 < 1 - Real.sqrt q := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG,memorySmallRowConstant q (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvsmall := hVs g
    positivity
  have hdelta : 0 ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) := by
    have hpv := mul_pos hP hv
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hdelta hrow) hB
  have hb := source_original_B409_orbit_actual_tilted_mass_collision_bound434
    P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
    Pmin vmin hP hv hV hVmin hPmin mu hmu hmu_pos
    SP sm cap sizes hsizes prime q Vs hq hq1 hVs
    zeta theta o k ho hk F B hB hF xs a t S hr
  have hR : C *
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,mu g p) ≤
      C * (1+2*((N+1:ℕ):ℝ)/Pmin)^((J+ell)*Fintype.card G) :=
        mul_le_mul_of_nonneg_left hMass hCnonneg
  exact hb.trans (by simpa only [C] using hR)
end Green64Analytic.CorrelationSquare

end

end

/-! ## EventualFullOrbitCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The genuine original tilted Fock-orbit collision under true prime growth
and BIG-group cap has eventually an absolute exp(1) tilted-mass overhead,
with no artificial normalization of the actual physicalSourceMuTilde law. -/
theorem eventually_source_original_B422_true_orbit_collision_exp_one434
    (c C0 : ℝ) (hc : 0 < c) (hC0 : 0 ≤ C0)
    (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
      (V : G → ℝ)
      (hGroups : (Fintype.card G : ℝ) ≤ C0 * Real.log L)
      (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
      (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
      (vmin : ℝ) (hv : 0<vmin)
      (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
      (hVmin : ∀ g,vmin≤V g)
      (hPrime : ∀ g p,p∈P g → Real.exp (L^c)≤(p:ℝ))
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
      (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
      (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
      (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
      (xs : GroupState SP sm (J+ell))
      (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ)
      (hr : sourceOriginalPhysicalReachable434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell)
        (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ P g})
          (fun _ p => p.val) (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434
            (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime a t)) S),
      let BP := fun g => {p : ℕ // p ∈ P g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V)
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs V (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V) K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V) V K q Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Real.exp (L^c)*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      Real.exp 1 := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc,
    eventually_source_original_B419_tilted_group_exponent_le_one434
      c C0 hc hC0 J ell] with L hSize hGroupsBudget
  intro G fi di P nz V hGroups ν hDisj Q hA hC xi hhA hhC hxi
    vmin hv hV hVmin hPrime SG fSG dSG SP fSP dSP sm nzSM cap sizes hsizes
    prime q Vs hq hq1 hVs zeta theta o k ho hk F B hB hF xs a t S hr
  dsimp only
  let N : ℕ := 2*Nat.ceil (L^(0.52:ℝ))
  let Pmin : ℝ := Real.exp (L^c)
  let e : ℝ := 2*((N+1:ℕ):ℝ)/Pmin
  let n : ℕ := (J+ell)*Fintype.card G
  let C : ℝ :=
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
       (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG,memorySmallRowConstant q (Vs g) ell) * B
  have hp : 0 < Pmin := Real.exp_pos _
  have hsize : ∀ g (p : {p : ℕ // p ∈ P g}),
      2*((N+1:ℕ):ℝ) ≤ (p.val:ℝ) := by
    intro g p
    exact hSize p.val (hPrime g p.val p.property)
  have hGroup : (n:ℝ)*e ≤ 1 := by
    simpa only [n,e,Pmin,N] using hGroupsBudget hGroups
  have he : 0 ≤ e := by dsimp [e,Pmin]; positivity
  have hPow : (1+e)^n ≤ Real.exp 1 :=
    source_original_B418_near_one_free_slot_exp_budget434 e he n hGroup
  have hsqrt : Real.sqrt q < 1 := by
    have hsq := Real.sq_sqrt hq.le
    have hn := Real.sqrt_nonneg q
    nlinarith only [hsq,hn,hq1]
  have hden : 0 < 1-Real.sqrt q := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG,memorySmallRowConstant q (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hdelta : 0 ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) := by
    have hpv := mul_pos hp hv
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hdelta hrow) hB
  have hPhysical := source_original_B421_sharp_physical_tilt_orbit_collision_bound434
    P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
    Pmin vmin hp hv hV hVmin (fun g p hp' => hPrime g p hp')
    N hsize SP sm cap sizes hsizes prime q Vs hq hq1 hVs
    zeta theta o k ho hk F B hB hF xs a t S hr
  have hAbsorb : C*(1+e)^n ≤ C*Real.exp 1 :=
    mul_le_mul_of_nonneg_left hPow hCnonneg
  exact hPhysical.trans (by simpa only [C,e,n,Pmin,N] using hAbsorb)
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualDataOrbitCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- B422 on the LITERAL original SourceComparisonData: true BIG alphabets,
harmonic source mass, q0, big-group cap and the original physical Fock orbit.
No normalized replacement law, no OLD or chronological history counting. -/
theorem eventually_source_original_B423_actual_data_orbit_collision434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
      (hTbLower : ∀ g p, p ∈ d.Tb g → Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,d.Vbig g=∑ p ∈ d.Tb g,1/(p:ℝ))
      (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
      (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
      (Vs : SG → ℝ)
      (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
      (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
      (xs : GroupState SP sm (J+ell))
      (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ d.Tb g}) J ell)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ)
      (hr : sourceOriginalPhysicalReachable434 SP sm
        (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
        (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
          (fun _ p => p.val) (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434
            (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime a t)) S),
      let BP := fun g => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 d.Tb d.Vbig J ell m hmJ ν
          Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig)
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        cfg.q0 1 Vs d.Vbig (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig) K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig) d.Vbig K cfg.q0 Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Real.exp (L^cfg.cexp)*cfg.vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B *
      Real.exp 1 := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B422_true_orbit_collision_exp_one434
      cfg.cexp cfg.C0 hc cfg.hC0 J ell m hmJ] with L hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    ν hDisj Q hA hC xi hhA hhC hxi SG fSG dSG
    SP fSP dSP sm nzSM cap sizes hsizes prime
    Vs hVs zeta theta o k ho hk F B hB hF xs a t S hr
  dsimp only
  exact hL d.Tb d.Vbig d.hBigGroups ν hDisj Q hA hC xi
    hhA hhC hxi cfg.vmin cfg.hv hVbig
    (fun g => d.hVbig g) hTbLower
    SP sm cap sizes hsizes prime cfg.q0 Vs cfg.hq0 cfg.hq1
    hVs zeta theta o k ho hk F B hB hF xs a t S hr
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualSmallSourceWeightedCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Weighted complex collision summation: the original nonnegative source
Haar mass is paid, never the cardinality of the source-state alphabet. -/
theorem source_original_B424_finite_subprob_collision_bound434
    {A : Type} [Fintype A] (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (htotal : (∑ a, w a) ≤ 1)
    (keep : A → Prop) [DecidablePred keep] (E : A → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ a, keep a → ‖E a‖ ≤ B) :
    ‖∑ a : A, if keep a then (w a : ℂ)*E a else 0‖ ≤ B := by
  calc
    _ ≤ ∑ a : A, ‖if keep a then (w a : ℂ)*E a else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a : A, w a * B := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : keep a
      · rw [if_pos h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw a)]
        exact mul_le_mul_of_nonneg_left (hE a h) (hw a)
      · rw [if_neg h, norm_zero]
        exact mul_nonneg (hw a) hB
    _ = (∑ a : A, w a)*B := by rw [Finset.sum_mul]
    _ ≤ B := by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right htotal hB)

/-- B422 on the LITERAL original SourceComparisonData: true BIG alphabets,
harmonic source mass, q0, big-group cap and the original physical Fock orbit.
Now integrate literal source SMALL Haar while retaining Fock/OLD and seen. -/
theorem eventually_source_original_B424_actual_SMALL_source_weighted_collision434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
      (hTbLower : ∀ g p, p ∈ d.Tb g → Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,d.Vbig g=∑ p ∈ d.Tb g,1/(p:ℝ))
      (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
      (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
      (Vs : SG → ℝ)
      (hVs : ∀ g,0<Vs g)
      (hVsHarmonic : ∀ g, Vs g = ∑ p : SP g, 1/(sm g p:ℝ))
      (zeta theta : ℝ) (o k : ℤ)
      (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
      (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ d.Tb g}) J ell)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ),
      let reachable := fun xs : GroupState SP sm (J+ell) => sourceOriginalPhysicalReachable434 SP sm
        (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
        (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
          (fun _ p => p.val) (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434
            (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime a t)) S
      let BP := fun g => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 d.Tb d.Vbig J ell m hmJ ν
          Q hA hC xi aux s t
      let collision := fun xs : GroupState SP sm (J+ell) =>
          fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig)
          (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
            J ell m cap patterns
            (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            cfg.q0 1 Vs d.Vbig (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig) K zeta theta o k st S F)
          (physicalFockProjection SP sm BP bm (J+ell) cap
            (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
              sizes hsizes prime a t)) -
          (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
            ∑ b : SourceOriginalB26Active434 BP J ell,
            ∑ ys : GroupState SP sm (J+ell),
            ∑ ss : GroupPermFamily (G := SG) (J+ell),
            ∑ tt : GroupPermFamily (G := SG) (J+ell),
              sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
                cap sizes hsizes prime patterns (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig) d.Vbig K cfg.q0 Vs zeta theta o k
                F xs ys a b t S h ss tt)
    ‖∑ xs : GroupState SP sm (J+ell),
      if reachable xs then
        (groupStateMass SP sm (J+ell) Vs : ℂ) * collision xs
      else 0‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Real.exp (L^cfg.cexp)*cfg.vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B *
      Real.exp 1 := by
  classical
  filter_upwards [eventually_source_original_B423_actual_data_orbit_collision434
      cfg J ell m hmJ] with L hPoint
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    ν hDisj Q hA hC xi hhA hhC hxi SG fSG dSG
    SP fSP dSP sm nzSM cap sizes hsizes prime
    Vs hVs hVsHarmonic zeta theta o k ho hk F B hB hF a t S
  dsimp only
  let W := GroupState SP sm (J+ell)
  let w : W → ℝ := fun xs => groupStateMass SP sm (J+ell) Vs
  let R : W → Prop := fun xs => sourceOriginalPhysicalReachable434 SP sm
    (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
    (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
      (fun _ p => p.val) (J+ell) cap
      (xs,sourceOriginalB26FrozenBigState434
        (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
        J ell cap sizes hsizes prime a t)) S
  let BP := fun g => {p : ℕ // p ∈ d.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let patterns : Unit → SourcePattern G J m := fun _ => pat
  let K : SourcePatternK BP J ell m patterns :=
    fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 d.Tb d.Vbig
      J ell m hmJ ν Q hA hC xi aux s t
  let E : W → ℂ := fun xs =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs
      (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig)
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        cfg.q0 1 Vs d.Vbig
        (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig)
        K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
    (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : W,
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
        sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns
          (physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) d.Vbig)
          d.Vbig K cfg.q0 Vs zeta theta o k F xs ys a b t S h ss tt)
  let C : ℝ :=
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Real.exp (L^cfg.cexp)*cfg.vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B * Real.exp 1
  have hw (xs : W) : 0 ≤ w xs := by
    dsimp only [w]
    unfold groupStateMass
    apply Finset.prod_nonneg
    intro g hg
    exact (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le
  have hTotal : (∑ xs : W, w xs) ≤ 1 := by
    simpa only [w,W] using
      (source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
        SP sm (J+ell) Vs hVs hVsHarmonic)
  have hLocal (xs : W) (hr : R xs) : ‖E xs‖ ≤ C := by
    have h := hPoint x Y Hprime d hTbLower hVbig
      ν hDisj Q hA hC xi hhA hhC hxi SP sm cap sizes hsizes prime
      Vs hVs zeta theta o k ho hk F B hB hF xs a t S hr
    simpa only [E,C,W,R,BP,bm,pat,patterns,K] using h
  have hsqrt : Real.sqrt cfg.q0 < 1 := by
    have hsq := Real.sq_sqrt cfg.hq0.le
    have hn := Real.sqrt_nonneg cfg.q0
    nlinarith only [hsq,hn,cfg.hq1]
  have hden : 0 < 1-Real.sqrt cfg.q0 := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hv := hVs g
    positivity
  have hdelta : 0 ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Real.exp (L^cfg.cexp)*cfg.vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) := by
    have hdenom := mul_pos (Real.exp_pos (L^cfg.cexp)) cfg.hv
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg hdelta hrow) hB)
      (Real.exp_pos _).le
  change ‖∑ xs : W, if R xs then (w xs : ℂ)*E xs else 0‖ ≤ C
  exact source_original_B424_finite_subprob_collision_bound434
    w hw hTotal R E C hCnonneg hLocal
end Green64Analytic.CorrelationSquare

end

end

/-! ## OrbitCollisionPowerSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The genuine original tilted Fock-orbit collision under true prime growth
and BIG-group cap has eventually an absolute exp(1) tilted-mass overhead,
with no artificial normalization of the actual physicalSourceMuTilde law. -/
theorem eventually_source_original_B424_true_orbit_collision_inverse_log434
    (c C0 vmin Cs Cslots D : ℝ) (Cq Cxi : ℕ)
    (hc : 0 < c) (hC0 : 0 ≤ C0) (hv : 0 < vmin) (hCs : 0 ≤ Cs)
    (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
      (V : G → ℝ)
      (hGroups : (Fintype.card G : ℝ) ≤ C0 * Real.log L)
      (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
      (hCard : ((ν.1.card+ν.2.card:ℕ):ℝ) ≤ Cs*Real.log L)
      (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
      (hVmin : ∀ g,vmin≤V g)
      (hPrime : ∀ g p,p∈P g → Real.exp (L^c)≤(p:ℝ))
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
      (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
      (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
      (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
      (xs : GroupState SP sm (J+ell))
      (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ)
      (hr : sourceOriginalPhysicalReachable434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell)
        (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ P g})
          (fun _ p => p.val) (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434
            (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime a t)) S),
      let BP := fun g => {p : ℕ // p ∈ P g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V)
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs V (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V) K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V) V K q Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      L^(-D) * ((∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B * Real.exp 1) := by
  filter_upwards [eventually_source_original_B422_true_orbit_collision_exp_one434
      c C0 hc hC0 J ell m hmJ,
    eventually_source_original_aux_ban_budget434
      c vmin Cs Cslots D Cq Cxi hc hv hCs] with L hOrbit hBudget
  intro G fG dG P nz V hGroups ν hDisj hCard Q hA hC xi hhA hhC hxi
    hSlots hQ hXi hV hVmin hPrime SG fSG dSG SP fSP dSP sm nzSM
    cap sizes hsizes prime q Vs hq hq1 hVs zeta theta o k ho hk
    F B hB hF xs a t S hr
  dsimp only
  have hOriginal := hOrbit P V hGroups ν hDisj Q hA hC xi hhA hhC hxi
    vmin hv hV hVmin hPrime SP sm cap sizes hsizes prime
    q Vs hq hq1 hVs zeta theta o k ho hk F B hB hF xs a t S hr
  let rate : ℝ :=
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
       (Real.exp (L^c)*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2))
  have hrate : rate ≤ L^(-D) := by
    simpa only [rate] using
      (hBudget.2 (ν.1.card+ν.2.card) (J+ell) Q xi
        hCard hSlots hQ hxi hXi)
  have hsqrt : Real.sqrt q < 1 := by
    have hsq := Real.sq_sqrt (le_of_lt hq)
    have hn := Real.sqrt_nonneg q
    nlinarith only [hsq,hn,hq1]
  have hden : 0 < 1-Real.sqrt q := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG,memorySmallRowConstant q (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hF : 0 ≤ (∏ g : SG,memorySmallRowConstant q (Vs g) ell) * B * Real.exp 1 :=
    mul_nonneg (mul_nonneg hrow hB) (Real.exp_pos _).le
  have habsorb := mul_le_mul_of_nonneg_right hrate hF
  exact hOriginal.trans (by convert habsorb using 1 <;> ring)
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualSourceDataCollisionPower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- At the literal SourceComparisonData BIG alphabet and original depth N(L),
the original Fock/OLD/seen orbit B26 collision costs at most exp(1) in tilted
free-slot mass; no normalization of physicalSourceMuTilde or history count. -/
theorem eventually_source_original_B425_true_source_data_collision_power434
    (cfg : SourceComparisonFixed434) (Cslots D : ℝ) (Cq Cxi : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
        (x Y Hprime : ℝ)
        (d : SourceComparisonData434 ι G cfg x L Y Hprime)
        [∀ g (p : {p : ℕ // p ∈ d.Tb g}),NeZero p.val]
        (hTbLower : ∀ g,∀ p ∈ d.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
        (hVbig : ∀ g,d.Vbig g=∑ p ∈ d.Tb g,1/(p:ℝ))
        (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
        (ν : SourceOriginalProbePattern434 G m)
        (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
        (Q : ℕ) (hA hC xi : ℝ)
        (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
        (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
        (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
        {SG : Type} [Fintype SG] [DecidableEq SG]
        (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
        (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
        (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
        (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
        (Vs : SG → ℝ) (hVs : ∀ g,0<Vs g)
        (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
        (F : FullPhysicalOutput SP sm
          (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
          → Finset ℕ → ℂ)
        (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
        (xs : GroupState SP sm (J+ell))
        (a : SourceOriginalB26Active434
          (fun g => {p : ℕ // p ∈ d.Tb g}) J ell)
        (t : SourceOriginalB26OldResidues434
          (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
          sizes prime) (S : Finset ℕ)
        (hr : sourceOriginalPhysicalReachable434 SP sm
          (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
          (physicalFockProjection SP sm
            (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
            (J+ell) cap (xs,sourceOriginalB26FrozenBigState434
              (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
              J ell cap sizes hsizes prime a t)) S),
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let N := 2*Nat.ceil (L^(0.52:ℝ))
      let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434
          d.Tb d.Vbig J ell m hmJ ν
          Q hA hC xi aux s t
      ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
          J ell m cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          cfg.q0 1 Vs d.Vbig mu K zeta theta o k st S F)
        (physicalFockProjection SP sm BP bm (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
            sizes hsizes prime a t)) -
        (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
          ∑ b : SourceOriginalB26Active434 BP J ell,
          ∑ ys : GroupState SP sm (J+ell),
          ∑ ss : GroupPermFamily (G := SG) (J+ell),
          ∑ tt : GroupPermFamily (G := SG) (J+ell),
            sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
              cap sizes hsizes prime patterns mu d.Vbig K cfg.q0 Vs
              zeta theta o k F xs ys a b t S h ss tt)‖ ≤
        L^(-D) * ((∏ g : SG,memorySmallRowConstant cfg.q0 (Vs g) ell) *
          B * Real.exp 1) := by
  let Cs : ℝ := (cfg.tmax:ℝ)*cfg.C0
  have hCs : 0 ≤ Cs := mul_nonneg (Nat.cast_nonneg _) cfg.hC0
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B424_true_orbit_collision_inverse_log434
    cfg.cexp cfg.C0 cfg.vmin Cs Cslots D Cq Cxi
    hc cfg.hC0 cfg.hv hCs J ell m hmJ,
    eventually_ge_atTop (1:ℝ)] with L hPow hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    blockA blockB hBlocks ν hν Q hA hC xi hhA hhC hxi hSlots hQ hXi
    SG fSG dSG SP fSP dSP sm nzsm cap sizes hsizes prime Vs hVs
    zeta theta o k ho hk F B hB hF xs a t S hr
  dsimp only
  have hG : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0 * Real.log L := by
    have hb : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hb : ((blockA.card+blockB.card:ℕ):ℝ) ≤
      (Fintype.card G:ℝ)).trans d.hBigGroups
  have hmem :=
    (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
  have hNA : ν.1.card ≤ blockA.card*m := by
    simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.1
  have hNB : ν.2.card ≤ blockB.card*m := by
    simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.2.2
  have hNat : ν.1.card+ν.2.card ≤ m*(blockA.card+blockB.card) := by
    nlinarith only [hNA,hNB]
  have hCard : ((ν.1.card+ν.2.card:ℕ):ℝ) ≤ Cs*Real.log L := by
    calc
      _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
      _ ≤ (m:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)
      _ ≤ (cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm)
          (mul_nonneg cfg.hC0 (Real.log_nonneg hL))
      _ = _ := by dsimp [Cs]; ring
  have hDisj : Disjoint ν.1 ν.2 :=
    source_original_probe_memory_actual_pattern_disjoint434
      blockA blockB hBlocks m ν hν
  have hVmin : ∀ g, cfg.vmin ≤ d.Vbig g := d.hVbig
  have hResult := hPow d.Tb d.Vbig d.hBigGroups ν hDisj hCard
    Q hA hC xi hhA hhC hxi hSlots hQ hXi hVbig hVmin hTbLower
    SP sm cap sizes hsizes prime cfg.q0 Vs cfg.hq0 cfg.hq1 hVs
    zeta theta o k ho hk F B hB hF xs a t S hr
  exact hResult
end Green64Analytic.CorrelationSquare

end

end

/-! ## OriginalAllNuOrbitCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal per-pattern original physical marked Fock orbit discrepancy;
this is the exact B425 left-hand side, not an abstract residual. -/
noncomputable def sourceOriginalB426NuOrbitCollision434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hC xi : ℝ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
    (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm
      (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
      → Finset ℕ → ℂ)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ d.Tb g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) : ℂ :=
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let N := 2*Nat.ceil (L^(0.52:ℝ))
      let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
      let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
      let patterns : Unit → SourcePattern G J m := fun _ => pat
      let K : SourcePatternK BP J ell m patterns :=
        fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434
          d.Tb d.Vbig J ell m hmJ ν
          Q hA hC xi aux s t
      fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
        (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
          J ell m cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          cfg.q0 1 Vs d.Vbig mu K zeta theta o k st S F)
        (physicalFockProjection SP sm BP bm (J+ell) cap
          (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
            sizes hsizes prime a t)) -
        (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
          ∑ b : SourceOriginalB26Active434 BP J ell,
          ∑ ys : GroupState SP sm (J+ell),
          ∑ ss : GroupPermFamily (G := SG) (J+ell),
          ∑ tt : GroupPermFamily (G := SG) (J+ell),
            sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
              cap sizes hsizes prime patterns mu d.Vbig K cfg.q0 Vs
              zeta theta o k F xs ys a b t S h ss tt)

/-- All original two-block probe patterns together, retaining per-pattern
mark-dependent physical Fock futures and arbitrary unit-modulus source signs.
The original family-cardinality loss is absorbed by choosing the B425
collision power before L; this is NOT primitive signed cancellation. -/
theorem eventually_source_original_B426_all_nu_orbit_collision_power434
    (cfg : SourceComparisonFixed434) (Cslots D : ℝ) (Cq Cxi : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
      (hTbLower : ∀ g p, p ∈ d.Tb g → Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi)
      (hA hC : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hA ν)
      (hhC : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hC ν)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
      (Vs : SG → ℝ) (hVs : ∀ g,0<Vs g)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : SourceOriginalProbePattern434 G m →
        FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
          (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ ν Y seen, ‖F ν Y seen‖≤B)
      (sign : SourceOriginalProbePattern434 G m → ℂ)
      (hSign : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        ‖sign ν‖ ≤ 1)
      (xs : GroupState SP sm (J+ell))
      (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ d.Tb g}) J ell)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ)
      (hr : sourceOriginalPhysicalReachable434 SP sm
        (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) (J+ell)
        (physicalFockProjection SP sm
          (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
          (J+ell) cap (xs, sourceOriginalB26FrozenBigState434
            (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime a t)) S),
      ‖∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sign ν * sourceOriginalB426NuOrbitCollision434
          d J ell m hmJ ν Q (hA ν) (hC ν) xi
          SP sm cap sizes hsizes prime Vs zeta theta o k
          (F ν) xs a t S‖ ≤
        L^(-D) * ((∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) *
          B * Real.exp 1) := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  filter_upwards [eventually_source_original_B425_true_source_data_collision_power434
      cfg Cslots (D+E) Cq Cxi J ell m hmJ hm,
    eventually_ge_atTop (1:ℝ)] with L hPer hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    blockA blockB hBlocks Q xi hxi hA hC hhA hhC hSlots hQ hXi
    SG fSG dSG SP fiSP diSP sm nzsm cap sizes hsizes prime Vs hVs
    zeta theta o k ho hk F B hB hF sign hSign xs a t S hr
  let fam := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let C : ℝ := (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B * Real.exp 1
  have hG : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hb : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hb : ((blockA.card+blockB.card:ℕ):ℝ) ≤
      (Fintype.card G:ℝ)).trans d.hBigGroups
  have hME : (m:ℝ)*cfg.C0*Real.log 2 ≤ E := by
    dsimp [E]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0)
      (Real.log_nonneg (by norm_num))
  have hFamily : (fam.card:ℝ) ≤ L^E := by
    exact (source_original_probe_family_log_power_card434
      blockA blockB m L cfg.C0 hL hG).trans
      (Real.rpow_le_rpow_of_exponent_le hL hME)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hRateNonneg : 0 ≤ L^(-(D+E)) := Real.rpow_nonneg hLp.le _
  have hcount : ((fam.card:ℝ)*L^(-(D+E))) ≤ L^(-D) := by
    calc
      _ ≤ L^E * L^(-(D+E)) :=
        mul_le_mul_of_nonneg_right hFamily hRateNonneg
      _ = L^(-D) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  have hsqrt : Real.sqrt cfg.q0 < 1 := by
    have hsq := Real.sq_sqrt cfg.hq0.le
    have hn := Real.sqrt_nonneg cfg.q0
    nlinarith only [hsq,hn,cfg.hq1]
  have hden : 0 < 1-Real.sqrt cfg.q0 := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hrow hB) (Real.exp_pos _).le
  have hScore : ((fam.card:ℝ)*L^(-(D+E)))*C ≤ L^(-D)*C :=
    mul_le_mul_of_nonneg_right hcount hCnonneg
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ fam) :
      ‖sourceOriginalB426NuOrbitCollision434
        d J ell m hmJ ν Q (hA ν) (hC ν) xi
        SP sm cap sizes hsizes prime Vs zeta theta o k
        (F ν) xs a t S‖ ≤ L^(-(D+E))*C := by
    have hOne := hPer x Y Hprime d hTbLower hVbig
      blockA blockB hBlocks ν hν
      Q (hA ν) (hC ν) xi (hhA ν hν) (hhC ν hν) hxi
      hSlots hQ hXi SP sm cap sizes hsizes prime Vs hVs
      zeta theta o k ho hk (F ν) B hB (hF ν)
      xs a t S hr
    exact hOne
  have hWeighted (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ fam) :
      ‖sign ν * sourceOriginalB426NuOrbitCollision434
        d J ell m hmJ ν Q (hA ν) (hC ν) xi
        SP sm cap sizes hsizes prime Vs zeta theta o k
        (F ν) xs a t S‖ ≤ L^(-(D+E))*C := by
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖sourceOriginalB426NuOrbitCollision434
          d J ell m hmJ ν Q (hA ν) (hC ν) xi
          SP sm cap sizes hsizes prime Vs zeta theta o k
          (F ν) xs a t S‖ :=
        mul_le_mul_of_nonneg_right (hSign ν hν) (norm_nonneg _)
      _ ≤ L^(-(D+E))*C := by simpa using hEach ν hν
  change ‖∑ ν ∈ fam, sign ν * sourceOriginalB426NuOrbitCollision434
      d J ell m hmJ ν Q (hA ν) (hC ν) xi
      SP sm cap sizes hsizes prime Vs zeta theta o k (F ν) xs a t S‖ ≤
      L^(-D)*C
  calc
    _ ≤ ∑ ν ∈ fam,
        ‖sign ν * sourceOriginalB426NuOrbitCollision434
          d J ell m hmJ ν Q (hA ν) (hC ν) xi
          SP sm cap sizes hsizes prime Vs zeta theta o k
          (F ν) xs a t S‖ := norm_sum_le _ _
    _ ≤ ∑ ν ∈ fam, L^(-(D+E))*C := by
      apply Finset.sum_le_sum
      intro ν hν
      exact hWeighted ν hν
    _ = ((fam.card:ℝ)*L^(-(D+E)))*C := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ L^(-D)*C := hScore
end Green64Analytic.CorrelationSquare

end

end

/-! ## FullInitialBirthCollision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- True original complete initial source BIG/SMALL law with globally
numerical birth-list Nodup and physical initial baseline. This replaces the
weaker BIG-only injectivity test of B428 by the ACTUAL original birth filter.
No initial Fock/vacuum or OLD sector is counted as an extra state. -/
theorem eventually_source_original_B429_full_initial_global_birth_power434
    (cfg : SourceComparisonFixed434) (Cslots D : ℝ) (Cq Cxi : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
      (hTbLower : ∀ g p, p ∈ d.Tb g → Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi)
      (hA hC : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hA ν)
      (hhC : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hC ν)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
      (Vs : SG → ℝ) (hVs : ∀ g,0<Vs g)
      (hVsHarmonic : ∀ g,Vs g=∑ p : SP g,1/(sm g p:ℝ))
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : SourceOriginalProbePattern434 G m →
        FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
          (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B) (hF : ∀ ν Y seen, ‖F ν Y seen‖≤B)
      (sign : SourceOriginalProbePattern434 G m → ℂ)
      (hSign : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        ‖sign ν‖ ≤ 1)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ),
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let R := Nat.ceil (L^(0.52:ℝ))
      let N := 2*R
      let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
      let A := SourceOriginalB26Active434 BP J ell
      let W := GroupState SP sm (J+ell)
      let initial : W → A → Prop := fun xs a =>
        (physicalOutputInitialBirths SP sm BP bm J ell
          (xs,fun g => (a g,0))).Nodup
      let reachable : W → A → Prop := fun xs a =>
        sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
          (physicalFockProjection SP sm BP bm (J+ell) cap
            (xs,sourceOriginalB26FrozenBigState434 BP bm J ell
              cap sizes hsizes prime a t)) S
      let baseline : ℝ :=
        ‖(physicalSourceBaselineProduct BP bm cfg.q0 N:ℂ)‖
      let weight : W × A → ℝ := fun z =>
        baseline * (groupStateMass SP sm (J+ell) Vs *
          (∏ g : G, activeMass (J+ell) (mu g) (z.2 g))) *
          (if initial z.1 z.2 then 1 else 0)
      let collision : W × A → ℂ := fun z =>
        ∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
          sign ν * sourceOriginalB426NuOrbitCollision434
            d J ell m hmJ ν Q (hA ν) (hC ν) xi
            SP sm cap sizes hsizes prime Vs zeta theta o k
            (F ν) z.1 z.2 t S
      ‖∑ z : W × A,
          if reachable z.1 z.2 then (weight z : ℂ) * collision z else 0‖ ≤
        L^(-D) * ((∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) *
          B * Real.exp 1) := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B426_all_nu_orbit_collision_power434
      cfg Cslots D Cq Cxi J ell m hmJ hm,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hAll hVisits hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    blockA blockB hBlocks Q xi hxi hA hC hhA hhC hSlots hQ hXi
    SG fSG dSG SP fiSP diSP sm nzsm cap sizes hsizes prime Vs hVs hVsHarmonic
    zeta theta o k ho hk F B hB hF sign hSign t S
  dsimp only
  let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
  let A := SourceOriginalB26Active434 BP J ell
  let W := GroupState SP sm (J+ell)
  let initial : W → A → Prop := fun xs a =>
    (physicalOutputInitialBirths SP sm BP bm J ell
      (xs,fun g => (a g,0))).Nodup
  let reachable : W → A → Prop := fun xs a =>
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell
          cap sizes hsizes prime a t)) S
  let baseline : ℝ := ‖(physicalSourceBaselineProduct BP bm cfg.q0 N:ℂ)‖
  let weight : W × A → ℝ := fun z =>
    baseline * (groupStateMass SP sm (J+ell) Vs *
      (∏ g : G, activeMass (J+ell) (mu g) (z.2 g))) *
      (if initial z.1 z.2 then 1 else 0)
  let collision : W × A → ℂ := fun z =>
    ∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sign ν * sourceOriginalB426NuOrbitCollision434
        d J ell m hmJ ν Q (hA ν) (hC ν) xi
        SP sm cap sizes hsizes prime Vs zeta theta o k
        (F ν) z.1 z.2 t S
  have hVpos : ∀ g : G, 0 < d.Vbig g :=
    fun g => cfg.hv.trans_le (d.hVbig g)
  have hVsub : ∀ g : G, (∑ p : BP g,1/(bm g p:ℝ)) = d.Vbig g := by
    intro g
    calc
      _ = ∑ p ∈ d.Tb g,(1:ℝ)/(p:ℝ) := by
        simpa only [BP,bm] using
          (Finset.sum_coe_sort (d.Tb g) (fun p : ℕ => (1:ℝ)/(p:ℝ)))
      _ = d.Vbig g := (hVbig g).symm
  have hsize : ∀ g (p : BP g), 2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ) := by
    intro g p
    exact hVisits p.val (hTbLower g p.val p.property)
  have hb : ∀ g (p : BP g), 0 < physicalSourceBaseline BP bm cfg.q0 N g p := by
    intro g p
    have hh := (source_original_B26_physical_baseline_half434
      BP bm cfg.q0 cfg.hq0.le cfg.hq1.le N g p (hsize g p)).1
    linarith only [hh]
  have hb1 : ∀ g (p : BP g), physicalSourceBaseline BP bm cfg.q0 N g p ≤ 1 := by
    intro g p
    exact (source_original_B26_physical_baseline_half434
      BP bm cfg.q0 cfg.hq0.le cfg.hq1.le N g p (hsize g p)).2
  have hmu : ∀ g (p : BP g), 0 ≤ mu g p := by
    intro g p
    exact (source_original_B410_physical_mu_tilde_positive_bound434
      BP bm cfg.q0 cfg.hq0.le cfg.hq1.le N d.Vbig hVpos hsize g p).1.le
  have hVac :
      sourceOriginalActualInitialVacuumMass434
        SP sm BP bm J ell cap cfg.q0 Vs d.Vbig R =
      baseline * (∑ xs : W,∑ a : A,
        (groupStateMass SP sm (J+ell) Vs *
          (∏ g : G, activeMass (J+ell) (mu g) (a g))) *
          (if initial xs a then (1:ℝ) else 0)) := by
    simpa only [baseline,A,W,mu,N,initial] using
      (source_original_ACTUAL_initial_mass_vacuum_factor434
        SP sm BP bm J ell cap cfg.q0 Vs hVs d.Vbig hVpos R hb)
  have hInitial :
      sourceOriginalActualInitialVacuumMass434
        SP sm BP bm J ell cap cfg.q0 Vs d.Vbig R ≤ 1 := by
    exact (source_original_ACTUAL_initial_mass_le_SMALL_mass434
      SP sm BP bm J ell cap cfg.q0 Vs hVs d.Vbig hVpos hVsub
      R hb hb1).trans
      (source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
        SP sm (J+ell) Vs hVs hVsHarmonic)
  have hweight (z : W × A) : 0 ≤ weight z := by
    have hsmall : 0 ≤ groupStateMass SP sm (J+ell) Vs := by
      unfold groupStateMass
      exact Finset.prod_nonneg (fun g hg =>
        (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le)
    have hbig : 0 ≤ (∏ g : G, activeMass (J+ell) (mu g) (z.2 g)) := by
      apply Finset.prod_nonneg
      intro g hg
      exact activeMass_nonneg (J+ell) (mu g) (hmu g) (z.2 g)
    by_cases hi : initial z.1 z.2
    · rw [show weight z = baseline *
          (groupStateMass SP sm (J+ell) Vs *
            (∏ g : G, activeMass (J+ell) (mu g) (z.2 g))) by
          simp only [weight,if_pos hi,mul_one]]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg hsmall hbig)
    · simp [weight,hi]
  have hTotal : (∑ z : W × A, weight z) ≤ 1 := by
    calc
      _ = baseline * (∑ xs : W, ∑ a : A,
        (groupStateMass SP sm (J+ell) Vs *
          (∏ g : G, activeMass (J+ell) (mu g) (a g))) *
          (if initial xs a then (1:ℝ) else 0)) := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro xs hxs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          dsimp only [weight]
          ring
      _ = sourceOriginalActualInitialVacuumMass434
          SP sm BP bm J ell cap cfg.q0 Vs d.Vbig R := hVac.symm
      _ ≤ 1 := hInitial
  let C : ℝ := L^(-D) *
    ((∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B * Real.exp 1)
  have hLocal (z : W × A) (hr : reachable z.1 z.2) :
      ‖collision z‖ ≤ C := by
    have h := hAll x Y Hprime d hTbLower hVbig
      blockA blockB hBlocks Q xi hxi hA hC hhA hhC hSlots hQ hXi
      SP sm cap sizes hsizes prime Vs hVs
      zeta theta o k ho hk F B hB hF sign hSign
      z.1 z.2 t S hr
    simpa only [collision,C,W,A] using h
  have hsqrt : Real.sqrt cfg.q0 < 1 := by
    have hsq := Real.sq_sqrt cfg.hq0.le
    have hn := Real.sqrt_nonneg cfg.q0
    nlinarith only [hsq,hn,cfg.hq1]
  have hden : 0 < 1-Real.sqrt cfg.q0 := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG,memorySmallRowConstant cfg.q0 (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg (by linarith only [hL]) _)
      (mul_nonneg (mul_nonneg hrow hB) (Real.exp_pos _).le)
  have h := source_original_B424_finite_subprob_collision_bound434
    weight hweight hTotal (fun z : W × A => reachable z.1 z.2)
    collision C hCnonneg hLocal
  change ‖∑ z : W × A,
    if reachable z.1 z.2 then (weight z : ℂ)*collision z else 0‖ ≤ C
  exact h
end Green64Analytic.CorrelationSquare

end

end

/-! ## FourSignCharacterCollisionRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

theorem source_original_B430_character_probability_mass434
    (k : ℤ) (hk : k ≠ 0) :
    (∑ _χ : DirichletCharacter ℂ k.natAbs,
       ‖((k.natAbs.totient:ℂ)⁻¹)‖) = 1 := by
  letI : NeZero k.natAbs := ⟨Nat.ne_of_gt (Int.natAbs_pos.mpr hk)⟩
  have hc : Fintype.card (DirichletCharacter ℂ k.natAbs) = k.natAbs.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k.natAbs
  have ht : (k.natAbs.totient:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr (Int.natAbs_pos.mpr hk))
  simp [hc,ht]

/-- Four true source projector signs (+,-,-,+)/4, with no scalar
residual substitution or post-square sign combination. -/
noncomputable def sourceOriginalB430ParityCoefficient (tw : Bool × Bool) : ℂ :=
  if tw.1 = tw.2 then 1/4 else -(1/4)

theorem source_original_B430_parity_norm434 (tw : Bool × Bool) :
    ‖sourceOriginalB430ParityCoefficient tw‖ = (1/4:ℝ) := by
  rcases tw with ⟨a,b⟩
  cases a <;> cases b <;> norm_num [sourceOriginalB430ParityCoefficient]

theorem source_original_B430_parity_mass434 :
    (∑ tw : Bool × Bool, ‖sourceOriginalB430ParityCoefficient tw‖) = 1 := by
  simp only [source_original_B430_parity_norm434]
  norm_num


/-- Uniform bound on four endpoint components implies a bound for the
COMPLETE source (+,-,-,+)/4 projector before the χ-square, with exact
normalized character mean. This theorem contains no scalar-sum transfer. -/
theorem source_original_B430_uniform_four_sign_character_RMS434
    (k : ℤ) (hk : k ≠ 0)
    (E : DirichletCharacter ℂ k.natAbs → Bool × Bool → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hEach : ∀ χ tw, ‖E χ tw‖ ≤ C) :
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖∑ tw : Bool × Bool,
          sourceOriginalB430ParityCoefficient tw * E χ tw‖^2) ≤ C^2 := by
  let a : ℝ := ‖((k.natAbs.totient:ℂ)⁻¹)‖
  have hA : (∑ _χ : DirichletCharacter ℂ k.natAbs, a) = 1 :=
    source_original_B430_character_probability_mass434 k hk
  have hProjected (χ : DirichletCharacter ℂ k.natAbs) :
      ‖∑ tw : Bool × Bool,
        sourceOriginalB430ParityCoefficient tw * E χ tw‖ ≤ C := by
    calc
      _ ≤ ∑ tw : Bool × Bool,
            ‖sourceOriginalB430ParityCoefficient tw * E χ tw‖ := norm_sum_le _ _
      _ = ∑ tw : Bool × Bool,
            ‖sourceOriginalB430ParityCoefficient tw‖ * ‖E χ tw‖ := by
              simp only [norm_mul]
      _ ≤ ∑ tw : Bool × Bool,
            ‖sourceOriginalB430ParityCoefficient tw‖ * C := by
              apply Finset.sum_le_sum
              intro tw htw
              exact mul_le_mul_of_nonneg_left (hEach χ tw) (norm_nonneg _)
      _ = C := by
        rw [← Finset.sum_mul,source_original_B430_parity_mass434,one_mul]
  have hSquared (χ : DirichletCharacter ℂ k.natAbs) :
      ‖∑ tw : Bool × Bool,
        sourceOriginalB430ParityCoefficient tw * E χ tw‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hProjected χ) 2
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ k.natAbs, a*C^2 := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact mul_le_mul_of_nonneg_left (hSquared χ) (norm_nonneg _)
    _ = (∑ _χ : DirichletCharacter ℂ k.natAbs, a)*C^2 := by rw [Finset.sum_mul]
    _ = C^2 := by rw [hA,one_mul]

/-- Identical signed endpoint order as the original native T four channels:
ff - tf - ft + tt, with both mixed channels negative. -/
theorem source_original_B430_four_projector_exact434
    (C : Bool → Bool → ℂ) :
    (∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw * C tw.1 tw.2) =
    (C false false - C true false - C false true + C true true) / 4 := by
  simp [Fintype.sum_prod_type,sourceOriginalB430ParityCoefficient]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## PhysicalB26ProjectedCharacterRMS -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Quantitative original B26 collision contribution AFTER the true
(+,-,-,+)/4 projector and BEFORE the exact 1/phi(|k|) character mean square.
Every χ and every physical endpoint sign may select a different bounded Fock
future; only the collision correction (not primitive signed RAW) is controlled.
No character/endpoint-count loss or normalized tilde-mu substitution. -/
theorem eventually_source_original_B431_full_initial_B26_projected_character_RMS434
    (cfg : SourceComparisonFixed434) (Cslots D : ℝ) (Cq Cxi : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
        [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ d.Tb g}), NeZero p.val]
      (hTbLower : ∀ g p, p ∈ d.Tb g → Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi)
      (hA hC : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hA ν)
      (hhC : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<hC ν)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ d.Tb g})
      (Vs : SG → ℝ) (hVs : ∀ g,0<Vs g)
      (hVsHarmonic : ∀ g,Vs g=∑ p : SP g,1/(sm g p:ℝ))
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F : DirichletCharacter ℂ k.natAbs → Bool × Bool →
        SourceOriginalProbePattern434 G m →
        FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ d.Tb g})
          (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
      (B : ℝ) (hB : 0≤B)
      (hF : ∀ χ tw ν Y seen, ‖F χ tw ν Y seen‖≤B)
      (sign : DirichletCharacter ℂ k.natAbs → Bool × Bool →
        SourceOriginalProbePattern434 G m → ℂ)
      (hSign : ∀ χ tw ν, ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
        ‖sign χ tw ν‖ ≤ 1)
      (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ d.Tb g})
        (fun _ p => p.val) sizes prime) (S : Finset ℕ),
      let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
      let bm : (g : G) → BP g → ℕ := fun _ p => p.val
      let R := Nat.ceil (L^(0.52:ℝ))
      let N := 2*R
      let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
      let A := SourceOriginalB26Active434 BP J ell
      let W := GroupState SP sm (J+ell)
      let initial : W → A → Prop := fun xs a =>
        (physicalOutputInitialBirths SP sm BP bm J ell
          (xs,fun g => (a g,0))).Nodup
      let reachable : W → A → Prop := fun xs a =>
        sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
          (physicalFockProjection SP sm BP bm (J+ell) cap
            (xs,sourceOriginalB26FrozenBigState434 BP bm J ell
              cap sizes hsizes prime a t)) S
      let baseline : ℝ :=
        ‖(physicalSourceBaselineProduct BP bm cfg.q0 N:ℂ)‖
      let weight : W × A → ℝ := fun z =>
        baseline * (groupStateMass SP sm (J+ell) Vs *
          (∏ g : G, activeMass (J+ell) (mu g) (z.2 g))) *
          (if initial z.1 z.2 then 1 else 0)
      let collision : DirichletCharacter ℂ k.natAbs → Bool × Bool → W × A → ℂ :=
        fun χ tw z =>
          ∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
            sign χ tw ν * sourceOriginalB426NuOrbitCollision434
              d J ell m hmJ ν Q (hA ν) (hC ν) xi
              SP sm cap sizes hsizes prime Vs zeta theta o k
              (F χ tw ν) z.1 z.2 t S
      let Err : DirichletCharacter ℂ k.natAbs → Bool × Bool → ℂ :=
        fun χ tw =>
          ∑ z : W × A,
            if reachable z.1 z.2 then
              (weight z : ℂ) * collision χ tw z
            else 0
      (∑ χ : DirichletCharacter ℂ k.natAbs,
        ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
          ‖∑ tw : Bool × Bool,
            sourceOriginalB430ParityCoefficient tw * Err χ tw‖^2) ≤
        (L^(-D) * ((∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) *
          B * Real.exp 1))^2 := by
  filter_upwards [eventually_source_original_B429_full_initial_global_birth_power434
      cfg Cslots D Cq Cxi J ell m hmJ hm,
    eventually_ge_atTop (1:ℝ)] with L hPer hL
  intro ι G fi di fG dG x Y Hprime d nz hTbLower hVbig
    blockA blockB hBlocks Q xi hxi hA hC hhA hhC hSlots hQ hXi
    SG fSG dSG SP fiSP diSP sm nzsm cap sizes hsizes prime Vs hVs hVsHarmonic
    zeta theta o k ho hk F B hB hF sign hSign t S
  dsimp only
  let BP := fun g : G => {p : ℕ // p ∈ d.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let R := Nat.ceil (L^(0.52:ℝ))
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm cfg.q0 N d.Vbig
  let A := SourceOriginalB26Active434 BP J ell
  let W := GroupState SP sm (J+ell)
  let initial : W → A → Prop := fun xs a =>
    (physicalOutputInitialBirths SP sm BP bm J ell
      (xs,fun g => (a g,0))).Nodup
  let reachable : W → A → Prop := fun xs a =>
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell
          cap sizes hsizes prime a t)) S
  let baseline : ℝ :=
    ‖(physicalSourceBaselineProduct BP bm cfg.q0 N:ℂ)‖
  let weight : W × A → ℝ := fun z =>
    baseline * (groupStateMass SP sm (J+ell) Vs *
      (∏ g : G, activeMass (J+ell) (mu g) (z.2 g))) *
      (if initial z.1 z.2 then 1 else 0)
  let collision : DirichletCharacter ℂ k.natAbs → Bool × Bool → W × A → ℂ :=
    fun χ tw z =>
      ∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sign χ tw ν * sourceOriginalB426NuOrbitCollision434
          d J ell m hmJ ν Q (hA ν) (hC ν) xi
          SP sm cap sizes hsizes prime Vs zeta theta o k
          (F χ tw ν) z.1 z.2 t S
  let Err : DirichletCharacter ℂ k.natAbs → Bool × Bool → ℂ :=
    fun χ tw =>
      ∑ z : W × A,
        if reachable z.1 z.2 then
          (weight z : ℂ) * collision χ tw z
        else 0
  let Bound : ℝ := L^(-D) *
    ((∏ g : SG, memorySmallRowConstant cfg.q0 (Vs g) ell) * B * Real.exp 1)
  have hE (χ : DirichletCharacter ℂ k.natAbs) (tw : Bool × Bool) :
      ‖Err χ tw‖ ≤ Bound := by
    have hh := hPer x Y Hprime d hTbLower hVbig
      blockA blockB hBlocks Q xi hxi hA hC hhA hhC hSlots hQ hXi
      SP sm cap sizes hsizes prime Vs hVs hVsHarmonic
      zeta theta o k ho hk (F χ tw) B hB (hF χ tw)
      (sign χ tw) (hSign χ tw) t S
    simpa only [Err,collision,Bound] using hh
  have hsqrt : Real.sqrt cfg.q0 < 1 := by
    have hsq := Real.sq_sqrt cfg.hq0.le
    have hn := Real.sqrt_nonneg cfg.q0
    nlinarith only [hsq,hn,cfg.hq1]
  have hden : 0 < 1-Real.sqrt cfg.q0 := sub_pos.mpr hsqrt
  have hrow : 0 ≤ (∏ g : SG,memorySmallRowConstant cfg.q0 (Vs g) ell) := by
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hBoundNonneg : 0 ≤ Bound := by
    dsimp [Bound]
    exact mul_nonneg (Real.rpow_nonneg (by linarith only [hL]) _)
      (mul_nonneg (mul_nonneg hrow hB) (Real.exp_pos _).le)
  have hRMS := source_original_B430_uniform_four_sign_character_RMS434
    k hk Err Bound hBoundNonneg hE
  simpa only [Bound] using hRMS
end Green64Analytic.CorrelationSquare

end

end

/-! ## TruePhysicalOuterCharacterTwists -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Outer |k|-character twisted source endpoint at the TRUE original ν-free
BIG marks. The conjugate is intentional: `star(sourceTest)` in the physical
pairing then carries χ(sourceX), matching the orientation of T's cofactor
factor before the source/cofactor identification. -/
noncomputable def sourceOriginalB432CharacterSourceTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (k : ℤ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (src : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
       (fun g : G => {p : ℕ // p ∈ d.Tb g})
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  star (χ ((sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
    (fun g i => (a g i).val) : ℕ) : ZMod k.natAbs)) * src ν a

/-- Corresponding literal original target BIG endpoint. -/
noncomputable def sourceOriginalB432CharacterTargetTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (k : ℤ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (tgt : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (b : SourceOriginalVariableBIGState434
       (fun g : G => {p : ℕ // p ∈ d.Tb g})
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  star (χ ((sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
    (fun g i => (b g i).val) : ℕ) : ZMod k.natAbs)) * tgt ν b

/-- Exact original SOURCE03 physical ν-pairing with outer χ included in
both actual mark-sensitive endpoint tests. The χ(m) χ̄(mp) factor is BEFORE
any character sum, Fourier average or norm square; no scalar-residual-to-RMS
transfer is used. This does not identify source BIG free products with T's
alpha cofactor indices (a distinct remaining source bridge). -/
theorem source_original_B432_true_physical_outer_character_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (src tgt : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun _ p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP free
    let w := sourceOriginalVariableBIGMass434 BP free mu
    sourceOriginalTrueNuSignedFullPhysicalPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      (sourceOriginalB432CharacterSourceTest434 d J ell m hmJ k χ src)
      (sourceOriginalB432CharacterTargetTest434 d J ell m hmJ k χ tgt) ν =
    ∑ ab : X × X,
      ((w ab.1 * w ab.2 : ℝ):ℂ) *
        (χ ((sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
             (fun g i => (ab.1 g i).val) : ℕ) : ZMod k.natAbs) *
         star (χ ((sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
             (fun g i => (ab.2 g i).val) : ℕ) : ZMod k.natAbs))) *
        (star (src ν ab.1) * tgt ν ab.2) *
        sourceOriginalProbeSignedMajorFourierError434
          J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val) := by
  dsimp [sourceOriginalTrueNuSignedFullPhysicalPairing434,
    sourceOriginalB432CharacterSourceTest434,
    sourceOriginalB432CharacterTargetTest434]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  simp only [map_mul, starRingEnd_apply, star_star]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## TrueCharacterTwistEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Physical SOURCE03 L² energy for the ORIGINAL dependent BIG free-slot
harmonic prime law cannot increase when a complex multiplier of modulus ≤1
is inserted at every source marked endpoint. This uses the real source
harmonic normalizer V_g; no uniform-counting replacement is made. -/
theorem source_original_B433_true_physical_test_multiplier_energy434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J)
    (mult test : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hMult : ∀ ν a, ‖mult ν a‖ ≤ 1)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun ν a => mult ν a * test ν a) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ test ν := by
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  have hVpos : ∀ g, 0 < d.Vbig g := fun g => cfg.hv.trans_le (d.hVbig g)
  have hEq : ∀ g, d.Vbig g = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
    intro g
    calc
      _ = ∑ p ∈ d.Tb g, 1/(p:ℝ) := hVbig g
      _ = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
        simpa only [BP] using
          (Finset.sum_coe_sort (d.Tb g) (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  have hmu : ∀ g (p : BP g), 0 ≤ mu g p :=
    (source_original_joint_harmonic_normalized434 BP
      (fun _ p => p.val) d.Vbig hVpos hEq).1
  have hw (a : SourceOriginalVariableBIGState434 BP free) :
      0 ≤ sourceOriginalVariableBIGMass434 BP free mu a :=
    source_original_variable_BIG_mass_nonneg434 BP free mu hmu a
  unfold sourceOriginalTrueNuSignedFullPhysicalEnergy434
  apply Finset.sum_le_sum
  intro a ha
  have hNorm : ‖mult ν a * test ν a‖ ≤ ‖test ν a‖ := by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hMult ν a) (norm_nonneg _)
  have hSq : ‖mult ν a * test ν a‖^2 ≤ ‖test ν a‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  exact mul_le_mul_of_nonneg_left hSq (hw a)

/-- Uniform in every *outer* character modulo actual |k|: the ORIGINAL
source χ(X_source)-twisted mark-sensitive C191 test costs no extra L² mass. -/
theorem source_original_B433_character_source_energy_le434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (k : ℤ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (src : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (sourceOriginalB432CharacterSourceTest434 d J ell m hmJ k χ src) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ src ν := by
  have h := source_original_B433_true_physical_test_multiplier_energy434
    d hVbig J ell m hmJ
    (fun η a => star (χ ((sourceOriginalProbeFreeSourceX434 J ell m hmJ η
      (fun g i => (a g i).val):ℕ) : ZMod k.natAbs))) src
    (by
      intro η a
      simpa only [norm_star] using χ.norm_le_one
        ((sourceOriginalProbeFreeSourceX434 J ell m hmJ η
           (fun g i => (a g i).val):ℕ) : ZMod k.natAbs)) ν
  change sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
    (fun η a => star (χ ((sourceOriginalProbeFreeSourceX434 J ell m hmJ η
       (fun g i => (a g i).val):ℕ) : ZMod k.natAbs)) * src η a) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ src ν
  exact h

/-- Same true physical C191 energy statement for the target endpoint, so
χ(sourceX) and χ̄(targetX) are both paid without a character-count loss. -/
theorem source_original_B433_character_target_energy_le434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (k : ℤ)
    (χ : DirichletCharacter ℂ k.natAbs)
    (tgt : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (sourceOriginalB432CharacterTargetTest434 d J ell m hmJ k χ tgt) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ tgt ν := by
  have h := source_original_B433_true_physical_test_multiplier_energy434
    d hVbig J ell m hmJ
    (fun η a => star (χ ((sourceOriginalProbeFreeTargetX434 J ell m hmJ η
      (fun g i => (a g i).val):ℕ) : ZMod k.natAbs))) tgt
    (by
      intro η a
      simpa only [norm_star] using χ.norm_le_one
        ((sourceOriginalProbeFreeTargetX434 J ell m hmJ η
           (fun g i => (a g i).val):ℕ) : ZMod k.natAbs)) ν
  change sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
    (fun η a => star (χ ((sourceOriginalProbeFreeTargetX434 J ell m hmJ η
       (fun g i => (a g i).val):ℕ) : ZMod k.natAbs)) * tgt η a) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ tgt ν
  exact h

/-- The original C191 dependent BIG-prime L² source/target energy is
nonnegative with the real variable V_g-normalized prime law. -/
theorem source_original_B433_true_physical_energy_nonneg434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J)
    (test : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
      d J ell m hmJ test ν := by
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  have hVpos : ∀ g, 0 < d.Vbig g := fun g => cfg.hv.trans_le (d.hVbig g)
  have hEq : ∀ g, d.Vbig g = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
    intro g
    calc
      _ = ∑ p ∈ d.Tb g, 1/(p:ℝ) := hVbig g
      _ = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
        simpa only [BP] using
          (Finset.sum_coe_sort (d.Tb g) (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  have hmu : ∀ g (p : BP g), 0 ≤ mu g p :=
    (source_original_joint_harmonic_normalized434 BP
      (fun _ p => p.val) d.Vbig hVpos hEq).1
  unfold sourceOriginalTrueNuSignedFullPhysicalEnergy434
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg
    (source_original_variable_BIG_mass_nonneg434 BP free mu hmu a)
    (sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMarkedCleanJointLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "BPerm" => BigGroupPerm (BG := BG) (J+ell)

/-- The coefficient of the ORIGINAL CLEAN witness sum. It keeps the
whole joint K, oriented phase, auxiliary ban, and actual birth-list Nodup.
The independent endpoint permutations are inverted only as coordinates. -/
def sourceOriginalMarkedCleanJointK434
    (nu : SourceOriginalProbePattern434 BG m)
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (sigma tau : BPerm)
    (K : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) → A → A → ℂ)
    (zeta theta : ℝ) (o k : ℤ) {R : Type}
    (d : Shared) (_r : R) (u : A) (_S : Finset ℕ) (v : A) : ℂ :=
  let a := (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma).symm u
  let b := (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).symm v
  let D := sourceOriginalB26FrozenD434 BP bm J ell m
    (sourceOriginalB26SmallTupleD434 SP sm J ell d)
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a sigma
  if ((o=1 ∨ o= -1) ∧ k≠0 ∧ sourceOriginalB26FrozenAuxBan434 BP J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a b) ∧
      (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) v).Nodup then
    originalEdgeScalar (K aux u v) zeta theta D o k
  else 0

/-- No artificial bounded future is used: only the explicit cap of the
original joint arithmetic coefficient is charged, exactly once. -/
theorem source_original_MARKED_CLEAN_joint_K_cap434
    (nu : SourceOriginalProbePattern434 BG m)
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (sigma tau : BPerm)
    (K : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) → A → A → ℂ)
    (zeta theta : ℝ) (o k : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ aux a b,‖K aux a b‖ ≤ C) {R : Type}
    (d : Shared) (r : R) (a : A) (S : Finset ℕ) (b : A) :
    ‖sourceOriginalMarkedCleanJointK434 SP sm BP bm J ell m hmJ nu aux sigma tau
      K zeta theta o k d r a S b‖ ≤ C := by
  unfold sourceOriginalMarkedCleanJointK434
  dsimp only
  split_ifs with h
  · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k h.1.1]
    exact hK aux a b
  · simpa only [norm_zero] using hC

variable (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))
local notation "Small" => GroupState SP sm (J+ell)
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- A complete actual auxiliary/four-permutation CLEAN channel equals
the corresponding slice of the literal original marked witness sum.
The only source hypothesis is its genuine active-in-seen condition. -/
theorem source_original_MARKED_CLEAN_frame_channel434
    (i : I)
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ)
    (hseen : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) a).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S)
    (r : SourceBigAux BP J m (patterns i) × (BPerm × BPerm) × (SPerm × SPerm)) :
    (sourceOriginalMarkedPhysicalFrameMass434 BP bm J ell m hmJ (nu i) Vb r:ℂ) *
      sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm J ell m hmJ (nu i)
        cap sizes hsizes prime r.1 o k q Vs Vb mu
        r.2.2.1 r.2.2.2 r.2.1.1 r.2.1.2
        (sourceOriginalMarkedCleanJointK434 SP sm BP bm J ell m hmJ (nu i)
          r.1 r.2.1.1 r.2.1.2 (K i) zeta theta o k)
        (fun ys b T u => sourceOriginalB26TargetPullback434 SP sm BP bm
          J ell cap sizes hsizes prime (fun Y => F Y T) ys b u) xs a S t =
    ∑ b : A,∑ ys : Small,
      sourceOriginalMarkedCleanIndexedTerm434 SP sm BP bm J ell m cap sizes hsizes prime
        patterns mu Vb K q Vs zeta theta o k F xs ys a b t S
        ⟨i,r.1,r.2.1.1,r.2.1.2⟩ r.2.2.1 r.2.2.2 := by
  unfold sourceOriginalMarkedPhysicalFrameMass434 sourceOriginalMarkedPhysicalCleanChannel434
  dsimp only
  rw [if_pos hseen,source_original_MARKED_PHYSICAL_divisor434,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold sourceOriginalMarkedCleanIndexedTerm434
  dsimp only
  simp only [source_original_MARKED_SMALL_shared_divisor434,
    source_original_MARKED_CLEAN_birth_set434]
  unfold sourceOriginalMarkedCleanJointK434 sourceOriginalB26FrozenPhysicalWeight434
  simp only [Equiv.symm_apply_apply]
  by_cases hd : Disjoint S
      ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ (nu i)
        (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) r.2.1.2 b)).image
        (fun p : Sigma BP => bm p.1 p.2))
  <;> by_cases hn : (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns i)
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) r.2.1.2 b)).Nodup
  <;> by_cases ha : (o=1 ∨ o= -1) ∧ k≠0 ∧ sourceOriginalB26FrozenAuxBan434 BP J ell m
      (patterns i) r.1 a b
  <;> dsimp only [sourceOriginalB26EndpointPermutationEquiv434,Equiv.coe_fn_mk] at hd hn ⊢
  <;> simp [hd,hn,ha]
  simp only [Finset.mul_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro ys hys
  simp only [source_original_B26_FROZEN_PHYSICAL_coefficient434]
  ring

end Green64Analytic.CorrelationSquare

end

end

