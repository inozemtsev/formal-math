module

public import Green64.Library.Weights.Part084
public import Green64.Library.Weights.B26ConductorFreeCleanBudget

@[expose] public section

/-!
# Weights / B26SharpCleanBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26SharpCleanBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000


/-- Exact factor removed from the original conductor-free budget at
the original q=1/2,ell=1 values. Pattern counts, tilted BIG masses,
residual m, and all source group masses are unchanged. -/
theorem source_original_B26_SHARP_RAW_budget_factor434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) :
    sourceOriginalB26RawFamilyHilbertBudget434 P J 1 m hmJ blockA blockB
      ((1:ℝ)/2) Vs mu =
    (16:ℝ)^(Fintype.card SG) *
      sourceOriginalB26SharpRawFamilyHilbertBudget434 P J 1 m hmJ blockA blockB
        ((1:ℝ)/2) Vs mu := by
  have h16 : ((4:ℝ)^(Fintype.card SG))^2 = (16:ℝ)^(Fintype.card SG) := by
    rw [←pow_mul,Nat.mul_comm (Fintype.card SG) 2,pow_mul]
    norm_num
  unfold sourceOriginalB26RawFamilyHilbertBudget434 sourceOriginalB26SharpRawFamilyHilbertBudget434
  rw [source_original_SMALL_sharp_cost_factor434 Vs hVs]
  simp only [mul_pow,h16,mul_assoc,←Finset.mul_sum]
  ring

private theorem complex_young (z w : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖z+w‖^2 ≤ (1+t)*‖z‖^2+(1+t⁻¹)*‖w‖^2 := by
  have hab : 2*‖z‖*‖w‖ ≤ t*‖z‖^2+t⁻¹*‖w‖^2 := by
    have hs : 0 ≤ (t*‖z‖-‖w‖)^2/t := div_nonneg (sq_nonneg _) ht.le
    have he : (t*‖z‖-‖w‖)^2/t = t*‖z‖^2+t⁻¹*‖w‖^2-2*‖z‖*‖w‖ := by
      field_simp [ht.ne']
      <;> ring
    rw [he] at hs
    linarith
  have hnorm := pow_le_pow_left₀ (norm_nonneg (z+w)) (norm_add_le z w) 2
  nlinarith

/-- Genuine full canonical CLEAN energy with sharper SMALL conditioning
and an arbitrarily small Young loss. The original arithmetic error theorem
is used at exponent 2*Bgoal. No new arithmetic or correlation premise is
introduced, and J is still fixed before the limit in L. -/
theorem eventually_source_original_B26_FULL_CLEAN_SHARP_YOUNG434
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
    ((1+L^(-Bgoal))*(sourceOriginalB26SharpRawFamilyHilbertBudget434 data.Tb J ell m hmJ
        blockA blockB q data.Vsmall mu + L^(-Bgoal)))*sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_FULL_ORDERED_CLEAN_RAW_SAVING434
      cfg gamma dscale (2*Bgoal) Cfreq Ck hgamma hd (by positivity) hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent J,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
      eventually_gt_atTop (0:ℝ)] with L hMain hVisit hL
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
  let budget := sourceOriginalB26SharpRawFamilyHilbertBudget434 data.Tb J ell m hmJ blockA blockB q data.Vsmall mu
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
  have hErr0 : E Err ≤ L^(-(2*Bgoal))*E f := by
    have ht := hBound.2
    rw [source_original_B26_NODUP_FULL_CLEAN_RAW_difference434] at ht
    exact ht
  have hRaw : E R ≤ budget*E f :=
    source_original_B26_SHARP_RAW_FULL_ORDERED_Hilbert434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt hq hq1 ho hi hmu f
  let t : ℝ := L^(-Bgoal)
  have ht : 0 < t := Real.rpow_pos_of_pos hL _
  have ht2 : t^2 = L^(-(2*Bgoal)) := by
    dsimp only [t]
    rw [pow_two,←Real.rpow_add hL]
    congr 1
    ring
  have hErr : E Err ≤ t^2*E f := by rw [ht2]; exact hErr0
  let w := sourceOriginalMemoryFullDensityMass434 SP sm BP (fun _ => Subtype.val)
    J ell cap data.Vsmall data.Vbig mu
  have hw (a : State) : 0 ≤ w a :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu hVs hVb hmu a
  have hp (a : State) (S : Finset ℕ) :
      ‖C a S‖^2 ≤ (1+t)*‖R a S‖^2+(1+t⁻¹)*‖Err a S‖^2 := by
    have he : C a S=R a S+Err a S := by dsimp [Err]; ring
    rw [he]
    exact complex_young (R a S) (Err a S) t ht
  have hTri : E C ≤ (1+t)*E R+(1+t⁻¹)*E Err := by
    calc
      _ ≤ ∑ a : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP (fun _ => Subtype.val)).powerset,
          ((1+t)*(w a*‖R a S‖^2)+(1+t⁻¹)*(w a*‖Err a S‖^2)) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro S hS
        have hh := mul_le_mul_of_nonneg_left (hp a S) (hw a)
        convert hh using 1 <;> ring
      _ = _ := by
        simp only [E,sourceOriginalMarkedOrderedEnergy434,w,
          mul_add,Finset.sum_add_distrib,Finset.mul_sum]
        rfl
  change E C ≤ ((1+t)*(budget+t))*E f
  calc
    _ ≤ (1+t)*E R+(1+t⁻¹)*E Err := hTri
    _ ≤ (1+t)*(budget*E f)+(1+t⁻¹)*(t^2*E f) :=
      add_le_add (mul_le_mul_of_nonneg_left hRaw (by positivity))
        (mul_le_mul_of_nonneg_left hErr (by positivity))
    _ = _ := by field_simp [ht.ne']; ring

end Green64Analytic.CorrelationSquare

end

end

