module

public import Green64.Library.Correlation.MarkedPhysicalCleanMean
public import Green64.Library.Correlation.Part046
public import Green64.Library.Correlation.Part048
public import Green64.Library.Weights.Part077
public import Green64.Library.Weights.MarkedSmallBigHilbert
public import Green64.Library.Analysis.Estimates.Part013

@[expose] public section

/-!
# Correlation / Part056

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedPhysicalSectorSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- All actual ordered OLD sectors, including repeated prime labels.
The factorials belong to the physical density, not to this index type. -/
abbrev SourceOriginalMarkedSectorIndex434 :=
  Σ n : ((g : BG) → Fin (cap g+1)), ((g : BG) → Fin (n g).val → BP g)

abbrev SourceOriginalMarkedSectorOld434
    (d : SourceOriginalMarkedSectorIndex434 BP cap) :=
  SourceOriginalB26OldResidues434 BP bm (fun g => (d.1 g).val) d.2

local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "Sector" => SourceOriginalMarkedSectorIndex434 BP cap

/-- Embed one actual frozen sector into the original ordered state. -/
def sourceOriginalMarkedSectorEmbed434
    (d : Sector) (xs : Small) (a : A)
    (t : SourceOriginalMarkedSectorOld434 BP bm cap d) : State :=
  (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
    (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 a t)

/-- Exact disjoint-sector coordinates of the complete original ordered
state space. Every indexed pending atom and its actual residue survives. -/
def sourceOriginalMarkedSectorEquiv434 :
    State ≃ Σ d : Sector,
      (Small × SourceOriginalMarkedSectorOld434 BP bm cap d) × A where
  toFun x := ⟨⟨fun g => (x.2 g).2.1,fun g i => ((x.2 g).2.2 i).1⟩,
    (x.1,fun g i => ((x.2 g).2.2 i).2),fun g => (x.2 g).1⟩
  invFun z := sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap
    z.1 z.2.1.1 z.2.2 z.2.1.2
  left_inv x := by rfl
  right_inv z := by
    rcases z with ⟨⟨n,p⟩,⟨xs,t⟩,a⟩
    rfl

/-- Reindex the FULL physical state sum, without multiplying by a
sector count or treating ordered OLD prime labels as independent tests. -/
theorem source_original_MARKED_full_sector_sum434
    {V : Type*} [AddCommMonoid V] (F : State → V) :
    (∑ x : State,F x) =
    ∑ d : Sector,∑ z : Small × SourceOriginalMarkedSectorOld434 BP bm cap d,
      ∑ a : A,F (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d z.1 a z.2) := by
  calc
    _ = ∑ z : (Σ d : Sector,
        (Small × SourceOriginalMarkedSectorOld434 BP bm cap d) × A),
        F ((sourceOriginalMarkedSectorEquiv434 SP sm BP bm J ell cap).symm z) := by
      apply Fintype.sum_equiv (sourceOriginalMarkedSectorEquiv434 SP sm BP bm J ell cap)
      intro x
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type]
      rfl

/-- Full ordered energy in the unchanged physical density and the
actual numerical birth-pool histories. -/
def sourceOriginalMarkedOrderedEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : State → Finset ℕ → ℂ) : ℝ :=
  ∑ x : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu x * ‖f x S‖^2

/-- Exact direct-sum identity for the previously verified frozen-sector
energy. Physical weights and all factorials are already in each term. -/
theorem source_original_MARKED_ordered_energy_sectors434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : State → Finset ℕ → ℂ) :
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu f =
    ∑ d : Sector,sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 Vs Vb mu
      (fun xs a S t => f (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d xs a t) S) := by
  unfold sourceOriginalMarkedOrderedEnergy434
  rw [source_original_MARKED_full_sector_sum434 SP sm BP bm J ell cap]
  apply Finset.sum_congr rfl
  intro d hd
  unfold sourceOriginalMarkedPhysicalSectorEnergy434
  apply Finset.sum_congr rfl
  intro z hz
  exact Finset.sum_comm

/-- Pulling a true orbit/history test back to ordered states preserves
its energy EXACTLY. The original weighted Fock orbit mass occurs once. -/
theorem source_original_MARKED_ordered_orbit_energy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : Out → Finset ℕ → ℂ) :
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (fun x S => F (physicalFockProjection SP sm BP bm (J+ell) cap x) S) =
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F := by
  letI : DecidableEq (FullPhysicalOutput SP sm BP bm (J+ell)) := Classical.decEq _
  let project := physicalFockProjection SP sm BP bm (J+ell) cap
  let w := sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu
  let mass := fun y => physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y
  have hm (y : Out) : mass y = ∑ x : State,if project x=y then w x else 0 := by
    symm
    simpa only [mass,w,project,Finset.sum_filter,sourceOriginalMemoryFullDensityMass434] using
      source_original_memory_sector_density_orbit_mass434 SP sm BP bm J ell cap Vs Vb mu y
  have hs (S : Finset ℕ) :
      (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,mass y*‖F y S‖^2) =
      ∑ x : State,w x*‖F (project x) S‖^2 := by
    simp_rw [hm,Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : project x ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap :=
      Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    rw [Finset.sum_eq_single (project x)]
    · simp
    · intro y hy hn
      exact if_neg (Ne.symm hn)
    · exact fun h => (h hx').elim
  unfold sourceOriginalMarkedOrderedEnergy434 sourceOriginalMemoryMarkedEnergy434
  change (∑ x : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    w x*‖F (project x) S‖^2) = _
  calc
    _ = ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ x : State,w x*‖F (project x) S‖^2 := Finset.sum_comm
    _ = ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,mass y*‖F y S‖^2 := by
      simp_rw [hs]
    _ = _ := Finset.sum_comm

/-- The actual weighted physical orbit compression is a contraction
also on the FULL joint numerical-history energy, with no history count. -/
theorem source_original_MARKED_orbit_compression_energy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g) (hmu : ∀ g p,0 < mu g p)
    (f : State → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (fun y S => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
        (fun x => f x S) y) ≤
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu f := by
  unfold sourceOriginalMemoryMarkedEnergy434 sourceOriginalMarkedOrderedEnergy434
  calc
    _ = ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
          sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y) *
          ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun x => f x S) y‖^2 :=
      Finset.sum_comm
    _ ≤ ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ x : State,sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu x *
          ‖f x S‖^2 := by
      apply Finset.sum_le_sum
      intro S hS
      exact source_original_memory_ORIGINAL_orbit_density_L2_contraction434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu (fun x => f x S)
    _ = _ := Finset.sum_comm

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26MarkedSmallComparison -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual two SMALL endpoint maps around the literal numerical
seen/residue comparison error. Shared SMALL labels determine their true
divisor; the target future keeps all active, OLD and history variables. -/
def sourceOriginalB26MarkedSmallComparison434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ p => p.val) J ell sizes prime
    q data.Vsmall ss
    (fun d => sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt
      (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
        J ell sizes prime q data.Vsmall tt f d))

/-- Quantitative coherent comparison error after BOTH genuine SMALL
endpoint maps, retaining complete OLD residues and numerical seen in one
arbitrary complex future. The same physical active density is used on
both sides. The fixed-sector SMALL Haar/Fock constant can be multiplied
on both sides without any cost; no count of sectors, histories or modes
is included. This does not estimate the full signed RAW chain or the
auxiliary-ban correction and does not construct SourceComparisonData. -/
theorem eventually_source_original_B26_MARKED_SMALL_COMPARISON_ERROR434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
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
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
      (f : Green64SmallHaar.GroupState SP sm (J+ell) →
        SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val) J ell sizes prime mu
      (sourceOriginalB26MarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  let Cs := sourceOriginalB26SmallNormExponent434 ell q cfg.vmin cfg.C0
  have hCs : 0 ≤ Cs :=
    source_original_B26_small_norm_exponent_nonneg434 ell q cfg.vmin cfg.C0 cfg.hC0
  let Bideal := Bgoal+2*Cs
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_PHYSICAL_NUMERIC_RESIDUE_COMPARISON_ERROR434
      cfg ell gamma dscale Bideal Cfreq Ck hgamma hd
      (add_nonneg hGoal (mul_nonneg (by norm_num) hCs)) hCk
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ zeta theta o k ho hZeta hk
    sigma tau epsSrc epsTgt ss tt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let Shared := SourceOriginalB26SharedTuple434 SP J ell
  let C := memorySmallGroupConditioningConstant (SG := ι) ell q data.Vsmall
  let delta := L^(-Bideal)
  let half := sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
    J ell sizes prime q data.Vsmall tt f
  let err := fun d : Shared =>
    sourceOriginalB26NumericResidueComparisonFamily434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt (half d)
  have hLocal (dsmall : ℕ) (hdsmall : 0 < dsmall)
      (F : SourceOriginalB26Active434 BP J ell → Finset ℕ →
        memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime → ℂ) :=
    hMain x Y Hprime data SP sm sizes prime q hq.le hq1.le sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ zeta k
      (fun _ => dsmall) (fun _ => theta) (fun _ => o)
      (fun _ _ => hdsmall) (fun _ _ => ho) hZeta hk sigma tau epsSrc epsTgt F
  refine ⟨(hLocal 1 (by norm_num) (fun _ _ _ => 0)).1,?_⟩
  have hErr (d : Shared) :
      sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu (err d) ≤
      delta*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu (half d) :=
    (hLocal _ (source_original_B26_small_tuple_positive434 SP sm J ell d) (half d)).2
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (cfg.hv.trans_le (data.hVbig g))
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hC : 0 ≤ C :=
    source_original_B26_small_conditioning_constant_nonneg434 ell q hq1 data.Vsmall hVs
  have hCap : C ≤ L^Cs := source_original_B26_small_conditioning_polynomial434
    ell q cfg.vmin cfg.C0 L hq hq1 cfg.hv cfg.hC0 hL
    data.Vsmall data.hVsmall data.hSmallGroups
  have hBudget : delta*C^2 ≤ L^(-Bgoal) :=
    source_original_B26_small_squared_budget434 L Bgoal Cs C hLp hC hCap
  have hHalf := source_original_MARKED_SMALL_half_energy434
    SP sm BP (fun _ p => p.val) J ell sizes prime q hq hq1 data.Vsmall hVs
    mu (fun g p => (hmu g p).le) tt f
  have hSynth := source_original_MARKED_SMALL_synthesis_energy434
    SP sm BP (fun _ p => p.val) J ell sizes prime q hq hq1 data.Vsmall hVs
    mu (fun g p => (hmu g p).le) ss err
  let Ein := sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
    J ell sizes prime mu f
  have hEin : 0 ≤ Ein := by
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro S hS
    exact source_original_B26_active_energy_nonneg434 BP J ell mu hmu (fun a => f z.1 a S z.2)
  calc
    _ ≤ C*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (err d)) := hSynth
    _ ≤ C*(∑ d : Shared,delta*sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (half d)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hErr d)) hC
    _ = (C*delta)*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (half d)) := by rw [← Finset.mul_sum];ring
    _ ≤ (C*delta)*(C*Ein) := mul_le_mul_of_nonneg_left hHalf (mul_nonneg hC hdelta)
    _ = (delta*C^2)*Ein := by ring
    _ ≤ L^(-Bgoal)*Ein := mul_le_mul_of_nonneg_right hBudget hEin

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26MarkedSmallAuxBan -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine auxiliary/ACTIVE ban correction through both SMALL endpoints,
with full OLD residues and the same numerical seen future. -/
def sourceOriginalB26MarkedSmallAuxBan434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ p => p.val) J ell sizes prime
    q data.Vsmall ss
    (fun d => sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt
      (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
        J ell sizes prime q data.Vsmall tt f d))


/-- Literal allowed auxiliary evolution minus RAW through both SMALL maps. -/
def sourceOriginalB26MarkedSmallCleanRaw434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ p => p.val) J ell sizes prime
    q data.Vsmall ss
    (fun d => sourceOriginalB26NumericResidueCleanRawFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt
      (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
        J ell sizes prime q data.Vsmall tt f d))


/-- Exact SMALL endpoint lifting of the comparison-minus-ban identity. -/
theorem source_original_B26_MARKED_SMALL_CLEAN_RAW_DECOMPOSITION434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26MarkedSmallCleanRaw434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f =
    fun xs a S r =>
      sourceOriginalB26MarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r -
      sourceOriginalB26MarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r := by
  funext xs a S r
  simp only [sourceOriginalB26MarkedSmallCleanRaw434,sourceOriginalB26MarkedSmallComparison434,
    sourceOriginalB26MarkedSmallAuxBan434,sourceOriginalMarkedSmallSynthesis434,
    sourceOriginalSmallEndpointSynthesis434,
    source_original_B26_NUMERIC_RESIDUE_CLEAN_RAW_DECOMPOSITION434,mul_sub]

/-- The true ban correction has arbitrary-power energy saving after both
SMALL maps. The slot bound remains explicit; no history count or bounded
future is assumed, and the original physical tilted density is unchanged. -/
theorem eventually_source_original_B26_MARKED_SMALL_AUX_BAN434
    (cfg : SourceComparisonFixed434) (ell : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (J : ℕ) (hmJ : m ≤ J)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (h xi : ℝ) (hh : 0<h) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
      (f : Green64SmallHaar.GroupState SP sm (J+ell) →
        SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val) J ell sizes prime mu
      (sourceOriginalB26MarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  let Cs := sourceOriginalB26SmallNormExponent434 ell q cfg.vmin cfg.C0
  let Bideal := Bgoal+2*Cs
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_PHYSICAL_NUMERIC_RESIDUE_AUX_BAN434
    cfg ell Cslots Bideal Cq Cxi,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hMain hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime hVbig hTbLower
    blockA blockB hBlocks m hm J hmJ hSlots Q h xi hh hxi hQ hXi zeta theta o k ho
    sigma tau epsSrc epsTgt ss tt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Shared := SourceOriginalB26SharedTuple434 SP J ell
  let C := memorySmallGroupConditioningConstant (SG := ι) ell q data.Vsmall
  let delta := L^(-Bideal)
  let half := sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
    J ell sizes prime q data.Vsmall tt f
  let err := fun d : Shared =>
    sourceOriginalB26NumericResidueAuxBanFamily434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt (half d)
  have hErr (d : Shared) :
      sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu (err d) ≤
      delta*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu (half d) :=
    hMain x Y Hprime data SP sm sizes prime q hq.le hq1.le hVbig hTbLower
      blockA blockB hBlocks J m hmJ hm hSlots Q h h xi hh hh hxi hQ hXi
      zeta k (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) (fun _ _ => ho) sigma tau epsSrc epsTgt (half d)
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (cfg.hv.trans_le (data.hVbig g))
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hC : 0 ≤ C :=
    source_original_B26_small_conditioning_constant_nonneg434 ell q hq1 data.Vsmall hVs
  have hCap : C ≤ L^Cs := source_original_B26_small_conditioning_polynomial434
    ell q cfg.vmin cfg.C0 L hq hq1 cfg.hv cfg.hC0 hL
    data.Vsmall data.hVsmall data.hSmallGroups
  have hBudget : delta*C^2 ≤ L^(-Bgoal) :=
    source_original_B26_small_squared_budget434 L Bgoal Cs C hLp hC hCap
  have hHalf := source_original_MARKED_SMALL_half_energy434
    SP sm BP (fun _ p => p.val) J ell sizes prime q hq hq1 data.Vsmall hVs
    mu (fun g p => (hmu g p).le) tt f
  have hSynth := source_original_MARKED_SMALL_synthesis_energy434
    SP sm BP (fun _ p => p.val) J ell sizes prime q hq hq1 data.Vsmall hVs
    mu (fun g p => (hmu g p).le) ss err
  let Ein := sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
    J ell sizes prime mu f
  have hEin : 0 ≤ Ein := by
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro S hS
    exact source_original_B26_active_energy_nonneg434 BP J ell mu hmu (fun a => f z.1 a S z.2)
  calc
    _ ≤ C*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (err d)) := hSynth
    _ ≤ C*(∑ d : Shared,delta*sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (half d)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hErr d)) hC
    _ = (C*delta)*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP
        (fun _ p => p.val) J ell mu (half d)) := by rw [← Finset.mul_sum];ring
    _ ≤ (C*delta)*(C*Ein) := mul_le_mul_of_nonneg_left hHalf (mul_nonneg hC hdelta)
    _ = (delta*C^2)*Ein := by ring
    _ ≤ L^(-Bgoal)*Ein := mul_le_mul_of_nonneg_right hBudget hEin


end Green64Analytic.CorrelationSquare

end

end

