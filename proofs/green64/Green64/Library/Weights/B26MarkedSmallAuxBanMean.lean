module

public import Green64.Library.Correlation.Part056
public import Green64.Library.Weights.B26MarkedSmallComparisonMean

@[expose] public section

/-!
# Weights / B26MarkedSmallAuxBanMean

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26MarkedSmallAuxBanMean -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem probability_history_energy
    {I X Z : Type} [Fintype I] [Fintype X] [Fintype Z]
    (pool : Finset ℕ) (w : X → ℝ) (hw : ∀ x,0 ≤ w x)
    (alpha : I → ℝ) (ha : ∀ i,0 ≤ alpha i) (htotal : (∑ i,alpha i)=1)
    (F : I → Z → X → Finset ℕ → ℂ) (C : ℝ)
    (hF : ∀ i,(∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖F i z x S‖^2) ≤ C) :
    (∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖∑ i,(alpha i:ℂ)*F i z x S‖^2) ≤ C := by
  have hp (z : Z) (S : Finset ℕ) (x : X) :
      ‖∑ i,(alpha i:ℂ)*F i z x S‖^2 ≤ ∑ i,alpha i*‖F i z x S‖^2 := by
    have h := source_original_finite_weighted_complex_kernel_CS434 alpha ha
      (fun _ => (1:ℂ)) (fun i => F i z x S)
    simpa only [one_mul,norm_one,one_pow,mul_one,htotal] using h
  calc
    _ ≤ ∑ z,∑ S ∈ pool.powerset,∑ x,w x*(∑ i,alpha i*‖F i z x S‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hp z S x) (hw x)
    _ = ∑ i,alpha i*(∑ z,∑ S ∈ pool.powerset,∑ x,w x*‖F i z x S‖^2) := by
      simp only [Finset.mul_sum]
      trans ∑ z,∑ S ∈ pool.powerset,∑ i,∑ x,alpha i*(w x*‖F i z x S‖^2)
      · apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro x hx
        ring
      trans ∑ z,∑ i,∑ S ∈ pool.powerset,∑ x,alpha i*(w x*‖F i z x S‖^2)
      · apply Finset.sum_congr rfl
        intro z hz
        exact Finset.sum_comm
      · exact Finset.sum_comm
    _ ≤ ∑ i,alpha i*C :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hF i) (ha i))
    _ = C := by rw [← Finset.sum_mul,htotal,one_mul]

/-- Both original normalized SMALL and BIG permutation means of the true ban correction. -/
def sourceOriginalB26MarkedSmallAuxBanMean434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let alpha := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell) *
    bigEndpointPairMass (BG := G) (J+ell)
  fun xs a S r =>
    ∑ st : (SPerm × SPerm) × (BPerm × BPerm),(alpha:ℂ) *
      sourceOriginalB26MarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
        epsSrc epsTgt st.1.1 st.1.2 f xs a S r

/-- Both original permutation means of the literal allowed-minus-RAW operator. -/
def sourceOriginalB26MarkedSmallCleanRawMean434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let alpha := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell) *
    bigEndpointPairMass (BG := G) (J+ell)
  fun xs a S r =>
    ∑ st : (SPerm × SPerm) × (BPerm × BPerm),(alpha:ℂ) *
      sourceOriginalB26MarkedSmallCleanRaw434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
        epsSrc epsTgt st.1.1 st.1.2 f xs a S r

/-- Exact coherent mean decomposition with one common coupled future. -/
theorem source_original_B26_MARKED_SMALL_MEAN_CLEAN_RAW_DECOMPOSITION434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26MarkedSmallCleanRawMean434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f =
    fun xs a S r =>
      sourceOriginalB26MarkedSmallComparisonMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f xs a S r -
      sourceOriginalB26MarkedSmallAuxBanMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f xs a S r := by
  funext xs a S r
  simp only [sourceOriginalB26MarkedSmallCleanRawMean434,
    sourceOriginalB26MarkedSmallComparisonMean434,sourceOriginalB26MarkedSmallAuxBanMean434,
    source_original_B26_MARKED_SMALL_CLEAN_RAW_DECOMPOSITION434,mul_sub,Finset.sum_sub_distrib]

/-- Normalized endpoint means retain the actual auxiliary-ban saving on
the complete coupled SMALL/active/seen/OLD future with no factorial cost. -/
theorem eventually_source_original_B26_MARKED_SMALL_AUX_BAN_MEAN434
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
      (epsSrc epsTgt : Bool)
      (f : Green64SmallHaar.GroupState SP sm (J+ell) →
        SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val) J ell sizes prime mu
      (sourceOriginalB26MarkedSmallAuxBanMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_MARKED_SMALL_AUX_BAN434
    cfg ell q hq hq1 Cslots Bgoal Cq Cxi,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc] with L hMain hVisit
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime hVbig hTbLower
    blockA blockB hBlocks m hm J hmJ hSlots Q h xi hh hxi hQ hXi zeta theta o k ho
    epsSrc epsTgt f
  classical
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let Index := (SPerm × SPerm) × (BPerm × BPerm)
  let cs := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell)
  let cb := bigEndpointPairMass (BG := G) (J+ell)
  let alpha := cs*cb
  let R := fun st : Index =>
    sourceOriginalB26MarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
      epsSrc epsTgt st.1.1 st.1.2 f
  have hLocal (st : Index) :=
    hMain x Y Hprime data SP sm sizes prime hVbig hTbLower
      blockA blockB hBlocks m hm J hmJ hSlots Q h xi hh hxi hQ hXi zeta theta o k ho
      (fun _ => st.2.1) (fun _ => st.2.2) epsSrc epsTgt st.1.1 st.1.2 f
  have hcs : 0 ≤ cs := by
    exact source_original_B26_big_permutation_mass_nonneg434 (G := ι) (J+ell)
  have hcb : 0 ≤ cb := source_original_B26_big_permutation_mass_nonneg434 (J+ell)
  have halpha : 0 ≤ alpha := mul_nonneg hcs hcb
  have hS : (∑ st : SPerm × SPerm,cs)=1 :=
    source_original_B26_big_permutation_mass_total434 (G := ι) (J+ell)
  have hB : (∑ st : BPerm × BPerm,cb)=1 :=
    source_original_B26_big_permutation_mass_total434 (J+ell)
  have htotal : (∑ st : Index,alpha)=1 := by
    change (∑ st : (SPerm × SPerm) × (BPerm × BPerm),cs*cb)=1
    calc
      _ = ∑ st : SPerm × SPerm,∑ bt : BPerm × BPerm,cs*cb :=
        Fintype.sum_prod_type _
      _ = ∑ st : SPerm × SPerm,cs := by
        apply Finset.sum_congr rfl
        intro st hst
        rw [← Finset.mul_sum,hB,mul_one]
      _ = 1 := hS
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
  exact probability_history_energy
    (Z := Green64SmallHaar.GroupState SP sm (J+ell) ×
      SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime)
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) w hw
    (fun _ : Index => alpha) (fun _ => halpha) htotal
    (fun st z a S => R st z.1 a S z.2)
    (L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f)
    (fun st => hLocal st)


end Green64Analytic.CorrelationSquare

end

end

