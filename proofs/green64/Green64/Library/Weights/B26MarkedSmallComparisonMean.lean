module

public import Green64.Library.Correlation.Part056

@[expose] public section

/-!
# Weights / B26MarkedSmallComparisonMean

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26MarkedSmallComparisonMean -/

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

/-- Both original normalized SMALL and BIG endpoint-pair means,
outside the coherent probe sum and acting on the same coupled future. -/
def sourceOriginalB26MarkedSmallComparisonMean434
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
      sourceOriginalB26MarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
        epsSrc epsTgt st.1.1 st.1.2 f xs a S r

/-- Genuine normalized SMALL and BIG permutation means preserve the
physical seen/OLD comparison saving. All four shared signs remain, and
no factorial, history, residue or frequency count is introduced. -/
theorem eventually_source_original_B26_MARKED_SMALL_COMPARISON_MEAN_ERROR434
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
      (sourceOriginalB26MarkedSmallComparisonMean434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_MARKED_SMALL_COMPARISON_ERROR434
      cfg gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hMain hVisit
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ zeta theta o k ho hZeta hk epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let Index := (SPerm × SPerm) × (BPerm × BPerm)
  let cs := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell)
  let cb := bigEndpointPairMass (BG := G) (J+ell)
  let alpha := cs*cb
  let R := fun st : Index =>
    sourceOriginalB26MarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
      epsSrc epsTgt st.1.1 st.1.2 f
  have hLocal (st : Index) :=
    hMain x Y Hprime data SP sm sizes prime sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ zeta theta o k ho hZeta hk
      (fun _ => st.2.1) (fun _ => st.2.2) epsSrc epsTgt st.1.1 st.1.2 f
  let ident : Index :=
    ⟨⟨fun _ => Equiv.refl _,fun _ => Equiv.refl _⟩,
      ⟨fun _ => Equiv.refl _,fun _ => Equiv.refl _⟩⟩
  refine ⟨(hLocal ident).1,?_⟩
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
    (fun st => (hLocal st).2)

end Green64Analytic.CorrelationSquare

end

end

