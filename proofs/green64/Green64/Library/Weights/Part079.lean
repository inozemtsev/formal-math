module

public import Green64.Library.Weights.B26NodupNumericFamily
public import Green64.Library.Weights.Part058
public import Green64.Library.Weights.B26TiltedAveragedAuxBan
public import Green64.Library.Weights.Part062
public import Green64.Library.Weights.Part077
public import Green64.Library.Correlation.Part056

@[expose] public section

/-!
# Weights / Part079

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26NodupNumericArithmetic -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine coherent all-pattern comparison ERROR on the physical
tilted active times numerical-seen space, at the original source depth.
Both endpoint permutations, actual birth-list Nodup and all four shared signs remain.
The future is arbitrary and may couple all active primes to the entire
history. No history-count loss or pointwise bound on the future occurs.

Only the polynomial number of probe patterns is charged. Its exponent
is chosen before the conductor and mesh; the threshold precedes J and
all moving source data. Auxiliary-ban, SMALL/OLD/Fock lifting and the
full RAW contribution are not asserted by this comparison-error bound. -/
theorem eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_ALL_NU_COMPARISON_ERROR434
    (cfg : SourceComparisonFixed434) (ell : ℕ)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (J : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal) * sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) cfg.hC0) hlog2
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_TILTED_HOMOGENEOUS_COMPARISON434
      cfg ell gamma dscale (Bgoal+E) Cfreq Ck hgamma hd (add_nonneg hGoal hE) hCk
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hMain hVisit hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1 sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ ζ k c theta orientation
    hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let delta := L^(-(Bgoal+E))
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast (data.hTbPrime g p.val p.property).pos
    exact one_div_pos.mpr (mul_pos (mul_pos
      (cfg.hv.trans_le (data.hVbig g)) hp) (hb g p))
  have hEnergy (U : A → ℂ) :
      0 ≤ sourceOriginalB26ActiveEnergy434 BP J ell mu U :=
    source_original_B26_active_energy_nonneg434 BP J ell mu hmu U
  have hAll (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ) (hET : 0 ≤ ET)
      (hcap : ∀ nu ∈ family,sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) ≤ ET) :=
    hMain x Y Hprime data q hq hq1 sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ ζ k c theta orientation
      hDivisor hOrientation hZeta hk sigma tau
      (sourceOriginalB26ActiveEnergy434 BP J ell mu U) ET (hEnergy U) hET
      (fun _ => U) V
      (fun nu _ => ⟨hEnergy U,le_rfl⟩)
      (fun nu hnu => ⟨hEnergy (V nu),hcap nu hnu⟩) epsSrc epsTgt
  have hModes := (hAll (fun _ => 0) (fun _ _ => 0) 0 (le_refl _)
    (by intro nu hnu; simp [sourceOriginalB26ActiveEnergy434])).1
  refine ⟨hModes,?_⟩
  have hBound := source_original_B26_NODUP_NUMERIC_COMPARISON_family_energy434
    data q N blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
    c theta orientation k sigma tau epsSrc epsTgt (fun g p => (hmu g p).le)
    delta hdelta (fun U V ET hET hcap => (hAll U V ET hET hcap).2) f
  have hCardNat : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_univ _
  have hCardReal : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) := by
    exact_mod_cast hCardNat
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L :=
    hCardReal.trans data.hBigGroups
  have hPower := source_original_probe_two_power_log_bound434
    blockA blockB m L cfg.C0 hL hGroups
  have hCount : (family.card:ℝ) ≤ (2:ℝ)^(m*(blockA.card+blockB.card)) := by
    exact_mod_cast source_original_two_block_probe_pattern_card434 blockA blockB m
  have hExp : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) cfg.hC0) hlog2
  have hCard : (family.card:ℝ) ≤ L^E :=
    hCount.trans (hPower.trans (Real.rpow_le_rpow_of_exponent_le hL hExp))
  have hBudget : delta*(family.card:ℝ) ≤ L^(-Bgoal) := by
    calc
      _ ≤ delta*L^E := mul_le_mul_of_nonneg_left hCard hdelta
      _ = L^(-Bgoal) := by
        dsimp only [delta]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  have hInput : 0 ≤ sourceOriginalB26NumericActiveEnergy434
      BP (fun _ p => p.val) J ell mu f := by
    exact Finset.sum_nonneg (fun S _ => hEnergy (fun s => f s S))
  exact hBound.trans (mul_le_mul_of_nonneg_right hBudget hInput)

/-- The actual auxiliary/ACTIVE ban has arbitrary-power energy saving
on physical tilted active primes times numerical seen, with actual birth-list Nodup.
Both permutations, all probe signs and arbitrary coupled futures remain.
The polynomial slot hypothesis is explicit and precedes no hidden limit. -/
theorem eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_ALL_NU_AUX_BAN434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (J m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (ho : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  let Ct := sourceOriginalB26TiltDensityExponent434 ell cfg.tmax cfg.C0
  let Dper : ℝ := Bgoal/2+3*E/2+Ct
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_canonical_aux_ban_saving434
    cfg.cexp cfg.vmin ((cfg.tmax:ℝ)*cfg.C0) Cslots Dper Cq Cxi
    hc cfg.hv (mul_nonneg (Nat.cast_nonneg _) cfg.hC0),
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hSave hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1
    hVbig hTbLower blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi
    hhA hhB hxi hQ hXi zeta k c theta orientation ho sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let delta := L^(-Dper)
  let per := delta^2*(L^Ct)^2
  let total := (family.card:ℝ)^2*per
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hper : 0 ≤ per := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have htotal : 0 ≤ total := mul_nonneg (sq_nonneg _) hper
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val) q N g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
  have hb0 (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := hb g p
    linarith only [hh]
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVEq (g : G) : data.Vbig g = ∑ p : BP g,1/(p.val:ℝ) := by
    rw [hVbig]
    simpa [BP] using (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).symm
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVpos g)
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb0 g p))
  have hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hnat : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hnat :
      ((blockA.card+blockB.card:ℕ):ℝ) ≤ (Fintype.card G:ℝ)).trans data.hBigGroups
  have hPattern (nu : Nu) (hnu : nu ∈ family) :
      ((nu.1.card+nu.2.card:ℕ):ℝ) ≤ ((cfg.tmax:ℝ)*cfg.C0)*Real.log L := by
    have hmem := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hnu
    have hNA : nu.1.card ≤ blockA.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.1
    have hNB : nu.2.card ≤ blockB.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.2.2
    have hNat : nu.1.card+nu.2.card ≤ m*(blockA.card+blockB.card) := by nlinarith only [hNA,hNB]
    calc
      _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
      _ ≤ (m:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
      _ ≤ (cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm)
          (mul_nonneg cfg.hC0 (Real.log_nonneg hL))
      _ = _ := by ring
  have hPair (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ) (hET : 0 ≤ ET)
      (hcap : ∀ nu ∈ family,sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) ≤ ET) :
      ‖∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q
          (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k sigma tau
          (fun _ => U) V nu‖^2 ≤
      total*sourceOriginalB26ActiveEnergy434 BP J ell mu U*ET := by
    let EU := sourceOriginalB26ActiveEnergy434 BP J ell mu U
    have hEU : 0 ≤ EU := source_original_B26_active_energy_nonneg434 BP J ell mu hmu U
    let pair := fun nu : Nu => sourceOriginalB26TiltedPermutedAuxBanPairing434
      data q N J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
      sigma tau (fun _ => U) V nu
    have hPer (nu : Nu) (hnu : nu ∈ family) :
        ‖pair nu‖^2 ≤ per*EU*sourceOriginalB26ActiveEnergy434 BP J ell mu (V nu) := by
      apply source_original_B26_physical_tilt_uniform_bilinear434
        BP (fun _ p => p.val) q N data.Vbig hVpos hVEq hb
        J ell m cfg.tmax hmJ hm nu (sigma nu) (tau nu) cfg.C0 L hL data.hBigGroups
        delta hdelta U (V nu)
      intro s t
      exact hSave data.Tb data.Vbig J ell m hmJ nu
        (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m nu hnu)
        Q hA hB xi hhA hhB hxi hVbig data.hVbig hTbLower (hPattern nu hnu)
        hSlots hQ hXi (c nu) s t (sigma nu) (tau nu)
        zeta (theta nu) (orientation nu) k (ho nu hnu)
    have hEach (nu : Nu) (hnu : nu ∈ family) :
        ‖sign nu*pair nu‖^2 ≤ (1:ℝ)^2*(per*EU*ET) := by
      have hs : ‖sign nu‖=1 := by
        dsimp only [sign,sourceOriginalB26NumericSharedSign434]
        rw [norm_mul]
        split_ifs <;> simp
      rw [norm_mul,hs,one_mul,one_pow,one_mul]
      exact (hPer nu hnu).trans
        (mul_le_mul_of_nonneg_left (hcap nu hnu) (mul_nonneg hper hEU))
    have hh := source_original_true_finite_weighted_minor_square434
      family (fun nu => sign nu*pair nu) (fun _ => (1:ℝ)) (per*EU*ET)
      (mul_nonneg (mul_nonneg hper hEU) hET) (by intro nu hnu;norm_num) hEach
    have hh' : ‖∑ nu ∈ family,sign nu*pair nu‖^2 ≤
        (family.card:ℝ)^2*(per*EU*ET) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    calc
      _ ≤ (family.card:ℝ)^2*(per*EU*ET) := hh'
      _ = _ := by dsimp only [total];ring
  have hBound := source_original_B26_NODUP_NUMERIC_AUX_BAN_family_energy434
    data q N blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta
    c theta orientation k sigma tau epsSrc epsTgt (fun g p => (hmu g p).le)
    total htotal hPair f
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0)
      (Real.log_nonneg (by norm_num))
  have hCard : (family.card:ℝ) ≤ L^E :=
    (source_original_probe_family_log_power_card434 blockA blockB m L cfg.C0 hL hGroups).trans
      (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hBudget : total*(family.card:ℝ) ≤ L^(-Bgoal) := by
    calc
      _ ≤ ((L^E)^2*per)*L^E :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hCard 2) hper)
          hCard (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _) hper)
      _ = L^(-Bgoal) := by
        dsimp only [per,delta]
        rw [← Real.rpow_two,← Real.rpow_two,← Real.rpow_two,
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,
          ← Real.rpow_add hLp,← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        dsimp only [Dper]
        ring
  have hInput : 0 ≤ sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell mu f :=
    Finset.sum_nonneg (fun S _ =>
      source_original_B26_active_energy_nonneg434 BP J ell mu hmu (fun s => f s S))
  exact hBound.trans (mul_le_mul_of_nonneg_right hBudget hInput)


end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NodupNumericResidue -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original auxiliary-minus-RAW evolution with coherent probe signs,
physical tilted fresh law, both endpoint permutations, full source-D
residue translations and the exact numerical no-rebirth update. -/
def sourceOriginalB26NodupNumericResidueComparisonFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) ∧
          sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val)
            J ell m hmJ nu (tau nu) t then
          sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0

/-- Exact all-frequency identity on the same active times seen carrier.
No sum is taken over histories, and the auxiliary divisor remains inside
its physical translation until the proved scalar Fourier identity is used. -/
theorem source_original_B26_NODUP_NUMERIC_RESIDUE_COMPARISON_FOURIER434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (hBlocks : Disjoint blockA blockB)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    sourceOriginalNumericSeenFourierLift434
      (fun psi => sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB
        J ell m hmJ Q hA hB xi zeta c
        (fun nu => theta nu+sourceOriginalB26ModeAngle434 SP sm
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
        orientation k sigma tau epsSrc epsTgt) f := by
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let angle := fun (psi : AddChar Torus ℂ) (nu : Nu) =>
    theta nu+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)
  let birth := fun (nu : Nu) (t : A) =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
        (fun p : Sigma BP => p.2.val)
  let valid := fun (nu : Nu) (t : A) =>
    sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val) J ell m hmJ nu (tau nu) t
  let law := fun (nu : Nu) (s t : A) =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu)
  let value := fun (psi : AddChar Torus ℂ) (nu : Nu) (s t : A) =>
    sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ nu
      Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
      zeta (angle psi nu) (orientation nu) k
  funext s S r
  unfold sourceOriginalNumericSeenFourierLift434
  simp only [Module.Basis.equivFun_symm_apply,AddChar.complexBasis_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hs : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  · dsimp only [BP] at hs
    have hterm (nu : Nu) (hnu : nu ∈ family) (t : A) :
        (if Disjoint S (birth nu t) ∧ valid nu t then
          sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig
            J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
            s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
            (f t (S∪birth nu t)) r else 0) =
        ∑ psi : AddChar Torus ℂ,
          (if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r := by
      by_cases hb : Disjoint S (birth nu t) ∧ valid nu t
      · simp only [if_pos hb]
        exact source_original_B26_RESIDUE_COMPARISON_FOURIER434
          SP sm data.Tb data.Vbig J ell m hmJ nu sizes prime
          Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
          zeta (theta nu) (orientation nu) k
          (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m nu hnu)
          (f t (S∪birth nu t)) r
      · simp [hb]
    have hcore (psi : AddChar Torus ℂ) :
        sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S =
        ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (if Disjoint S (birth nu t) ∧ valid nu t then value psi nu s t *
            (AddChar.complexBasis Torus).equivFun (f t (S∪birth nu t)) psi else 0) := by
      unfold sourceOriginalB26NodupNumericComparisonFamily434 sourceOriginalB26NumericPermutedClean434
      dsimp only
      simp only [if_pos hs]
      apply Finset.sum_congr rfl
      intro nu hnu
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      change law nu s t *
        (if Disjoint S (birth nu t) then value psi nu s t *
          (if valid nu t then (AddChar.complexBasis Torus).equivFun
            (f t (S∪birth nu t)) psi else 0) else 0) =
        law nu s t * (if Disjoint S (birth nu t) ∧ valid nu t then
          value psi nu s t*(AddChar.complexBasis Torus).equivFun
            (f t (S∪birth nu t)) psi else 0)
      by_cases hb : Disjoint S (birth nu t) <;>
        by_cases hn : valid nu t <;> simp [hb,hn]
    change sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k sigma tau
      epsSrc epsTgt f s S r =
      ∑ psi : AddChar Torus ℂ,
        sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S * psi r
    simp_rw [hcore]
    unfold sourceOriginalB26NodupNumericResidueComparisonFamily434
    dsimp only
    rw [if_pos hs]
    change (∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
      (if Disjoint S (birth nu t) ∧ valid nu t then
        sourceOriginalB26ResidueComparisonValue434 SP sm data.Tb data.Vbig
          J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
          s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r else 0)) = _
    calc
      _ = ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (∑ psi : AddChar Torus ℂ,(if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [hterm nu hnu t]
      _ = _ := by
        simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        trans ∑ nu ∈ family,∑ psi : AddChar Torus ℂ,∑ t : A,
          sign nu*(law nu s t*((if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r))
        · apply Finset.sum_congr rfl
          intro nu hnu
          exact Finset.sum_comm
        · exact Finset.sum_comm
  · dsimp only [BP] at hs
    simp [sourceOriginalB26NodupNumericResidueComparisonFamily434,
      sourceOriginalB26NodupNumericComparisonFamily434,sourceOriginalB26NumericPermutedClean434,hs]


/-- Original auxiliary/ACTIVE ban correction with coherent probe signs,
physical tilted fresh law, both endpoint permutations, full source-D
residue translations and the exact numerical no-rebirth update. -/
def sourceOriginalB26NodupNumericResidueAuxBanFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) ∧
          sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val)
            J ell m hmJ nu (tau nu) t then
          sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0

/-- Exact all-frequency identity on the same active times seen carrier.
No sum is taken over histories, and the auxiliary divisor remains inside
its physical translation until the proved scalar Fourier identity is used. -/
theorem source_original_B26_NODUP_NUMERIC_RESIDUE_AUX_BAN_FOURIER434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    sourceOriginalNumericSeenFourierLift434
      (fun psi => sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB
        J ell m hmJ Q hA hB xi zeta c
        (fun nu => theta nu+sourceOriginalB26ModeAngle434 SP sm
          (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
        orientation k sigma tau epsSrc epsTgt) f := by
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let Nu := SourceOriginalProbePattern434 G m
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let angle := fun (psi : AddChar Torus ℂ) (nu : Nu) =>
    theta nu+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)
  let birth := fun (nu : Nu) (t : A) =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
        (fun p : Sigma BP => p.2.val)
  let valid := fun (nu : Nu) (t : A) =>
    sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val) J ell m hmJ nu (tau nu) t
  let law := fun (nu : Nu) (s t : A) =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu)
  let value := fun (psi : AddChar Torus ℂ) (nu : Nu) (s t : A) =>
    sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu
      Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
      zeta (angle psi nu) (orientation nu) k
  funext s S r
  unfold sourceOriginalNumericSeenFourierLift434
  simp only [Module.Basis.equivFun_symm_apply,AddChar.complexBasis_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hs : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  · dsimp only [BP] at hs
    have hterm (nu : Nu) (hnu : nu ∈ family) (t : A) :
        (if Disjoint S (birth nu t) ∧ valid nu t then
          sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig
            J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
            s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
            (f t (S∪birth nu t)) r else 0) =
        ∑ psi : AddChar Torus ℂ,
          (if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r := by
      by_cases hb : Disjoint S (birth nu t) ∧ valid nu t
      · simp only [if_pos hb]
        exact source_original_B26_RESIDUE_AUX_BAN_FOURIER434
          SP sm data.Tb data.Vbig J ell m hmJ nu sizes prime
          Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
          zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r
      · simp [hb]
    have hcore (psi : AddChar Torus ℂ) :
        sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S =
        ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (if Disjoint S (birth nu t) ∧ valid nu t then value psi nu s t *
            (AddChar.complexBasis Torus).equivFun (f t (S∪birth nu t)) psi else 0) := by
      dsimp only [sourceOriginalB26NodupNumericAuxBanFamily434]
      rw [if_pos hs]
      apply Finset.sum_congr rfl
      intro nu hnu
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      change law nu s t *
        (if Disjoint S (birth nu t) then value psi nu s t *
          (if valid nu t then (AddChar.complexBasis Torus).equivFun
            (f t (S∪birth nu t)) psi else 0) else 0) =
        law nu s t * (if Disjoint S (birth nu t) ∧ valid nu t then
          value psi nu s t*(AddChar.complexBasis Torus).equivFun
            (f t (S∪birth nu t)) psi else 0)
      by_cases hb : Disjoint S (birth nu t) <;>
        by_cases hn : valid nu t <;> simp [hb,hn]
    change sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k sigma tau
      epsSrc epsTgt f s S r =
      ∑ psi : AddChar Torus ℂ,
        sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
          hA hB xi zeta c (angle psi) orientation k sigma tau epsSrc epsTgt
          (fun t T => (AddChar.complexBasis Torus).equivFun (f t T) psi) s S * psi r
    simp_rw [hcore]
    unfold sourceOriginalB26NodupNumericResidueAuxBanFamily434
    dsimp only
    rw [if_pos hs]
    change (∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
      (if Disjoint S (birth nu t) ∧ valid nu t then
        sourceOriginalB26ResidueAuxBanValue434 SP sm data.Tb data.Vbig
          J ell m hmJ nu sizes prime Q (hA nu) (hB nu) xi (c nu)
          s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
          (f t (S∪birth nu t)) r else 0)) = _
    calc
      _ = ∑ nu ∈ family,sign nu*∑ t : A,law nu s t *
          (∑ psi : AddChar Torus ℂ,(if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [hterm nu hnu t]
      _ = _ := by
        simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        trans ∑ nu ∈ family,∑ psi : AddChar Torus ℂ,∑ t : A,
          sign nu*(law nu s t*((if Disjoint S (birth nu t) ∧ valid nu t then
            value psi nu s t*(AddChar.complexBasis Torus).equivFun
              (f t (S∪birth nu t)) psi else 0)*psi r))
        · apply Finset.sum_congr rfl
          intro nu hnu
          exact Finset.sum_comm
        · exact Finset.sum_comm
  · dsimp only [BP] at hs
    simp [sourceOriginalB26NodupNumericResidueAuxBanFamily434,
      sourceOriginalB26NodupNumericAuxBanFamily434,hs]


/-- Literal allowed auxiliary evolution minus RAW on numerical seen. -/
def sourceOriginalB26NodupNumericResidueCleanRawFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (s : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell)
    (S : Finset ℕ)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => Subtype.val) sizes prime) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)) ∧
          sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val)
            J ell m hmJ nu (tau nu) t then
          sourceOriginalB26ResidueCleanRawValue434 SP sm data.Tb data.Vbig J ell m hmJ nu
            sizes prime Q (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k
            (f t (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
                (fun p : Sigma BP => p.2.val))) r
         else 0)
  else 0


/-- Exact comparison-minus-ban decomposition on the same coupled future,
with coherent signs and every actual pattern-dependent history update. -/
theorem source_original_B26_NODUP_NUMERIC_RESIDUE_CLEAN_RAW_DECOMPOSITION434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NodupNumericResidueCleanRawFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    fun s S r =>
      sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f s S r -
      sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f s S r := by
  classical
  funext s S r
  unfold sourceOriginalB26NodupNumericResidueCleanRawFamily434
    sourceOriginalB26NodupNumericResidueComparisonFamily434 sourceOriginalB26NodupNumericResidueAuxBanFamily434
  dsimp only
  split_ifs with hs
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro nu hnu
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← mul_sub]
    congr 1
    split_ifs <;> simp only [source_original_B26_RESIDUE_CLEAN_RAW_DECOMPOSITION434,sub_self]
  · simp


end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NodupResidueArithmetic -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Arithmetic saving for the LITERAL unbanned auxiliary-minus-RAW
evolution on physical tilted active primes times numerical seen times
the complete original frozen SMALL/OLD residue group. Every auxiliary
and RAW divisor is translated separately before Fourier expansion.
Both endpoint permutations, coherent probe signs and arbitrary coupled
complex futures remain present. There is no residue/frequency/history
count loss. The source threshold precedes every moving OLD sector.

SMALL half-map synthesis, the auxiliary ban and global RAW-chain control
are separate from this theorem. The SourceComparisonData fields remain
explicit; no constructor or original global correlation is asserted. -/
theorem eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_RESIDUE_COMPARISON_ERROR434
    (cfg : SourceComparisonFixed434) (ell : ℕ)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
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
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
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
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<c nu)
      (hOrientation : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_ALL_NU_COMPARISON_ERROR434
      cfg ell gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent] with L hMain
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime q hq hq1
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J hmJ zeta k c theta orientation
    hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  have hLocal (angle : SourceOriginalProbePattern434 G m → ℝ)
      (g : A → Finset ℕ → ℂ) :=
    hMain x Y Hprime data q hq hq1 sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
      blockA blockB hDisjoint m hm J hmJ zeta k c angle orientation
      hDivisor hOrientation hZeta hk sigma tau epsSrc epsTgt g
  refine ⟨(hLocal theta (fun _ _ => 0)).1,?_⟩
  rw [source_original_B26_NODUP_NUMERIC_RESIDUE_COMPARISON_FOURIER434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta c theta orientation k
    sigma tau epsSrc epsTgt hDisjoint f]
  apply source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val))
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) (L^(-Bgoal))
  intro psi g
  exact (hLocal (fun nu => theta nu+sourceOriginalB26ModeAngle434
    SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi)) g).2


/-- Actual auxiliary/ACTIVE ban saving on physical active times seen
times the complete SMALL/OLD residue group, with its literal divisor
translations. No residue, character, or history count is incurred. -/
theorem eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_RESIDUE_AUX_BAN434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (J m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (zeta : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (ho : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation nu=1 ∨ orientation nu= -1)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (epsSrc epsTgt : Bool)
      (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
        Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
          (fun _ => Subtype.val) sizes prime → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu
      (sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N
        blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
        sigma tau epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalB26NumericResidueEnergy434 BP (fun _ p => p.val) J ell mu f := by
  filter_upwards [eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_ALL_NU_AUX_BAN434
    cfg ell Cslots Bgoal Cq Cxi] with L hMain
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig sizes prime q hq hq1
    hVbig hTbLower blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi
    hhA hhB hxi hQ hXi zeta k c theta orientation ho sigma tau epsSrc epsTgt f
  classical
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let A := SourceOriginalB26Active434 BP J ell
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let Torus := memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes prime
  rw [source_original_B26_NODUP_NUMERIC_RESIDUE_AUX_BAN_FOURIER434 data SP sm sizes prime q N
    blockA blockB J ell m hmJ Q (fun _ => hA) (fun _ => hB) xi zeta c theta orientation k
    sigma tau epsSrc epsTgt f]
  apply source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val))
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) (L^(-Bgoal))
  intro psi g
  exact hMain x Y Hprime data q hq hq1 hVbig hTbLower
    blockA blockB hBlocks J m hmJ hm hSlots Q hA hB xi hhA hhB hxi hQ hXi
    zeta k c (fun nu => theta nu+sourceOriginalB26ModeAngle434
      SP sm BP (fun _ => Subtype.val) sizes prime psi/(2*Real.pi))
    orientation ho sigma tau epsSrc epsTgt g


end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NodupMarkedSmall -/

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
def sourceOriginalB26NodupMarkedSmallComparison434
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
    (fun d => sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N
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
theorem eventually_source_original_B26_NODUP_MARKED_SMALL_COMPARISON_ERROR434
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
      (sourceOriginalB26NodupMarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  let Cs := sourceOriginalB26SmallNormExponent434 ell q cfg.vmin cfg.C0
  have hCs : 0 ≤ Cs :=
    source_original_B26_small_norm_exponent_nonneg434 ell q cfg.vmin cfg.C0 cfg.hC0
  let Bideal := Bgoal+2*Cs
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_RESIDUE_COMPARISON_ERROR434
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
    sourceOriginalB26NodupNumericResidueComparisonFamily434 data SP sm sizes prime q N blockA blockB
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


/-- Genuine auxiliary/ACTIVE ban correction through both SMALL endpoints,
with full OLD residues and the same numerical seen future. -/
def sourceOriginalB26NodupMarkedSmallAuxBan434
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
    (fun d => sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt
      (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
        J ell sizes prime q data.Vsmall tt f d))


/-- Literal allowed auxiliary evolution minus RAW through both SMALL maps. -/
def sourceOriginalB26NodupMarkedSmallCleanRaw434
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
    (fun d => sourceOriginalB26NodupNumericResidueCleanRawFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q (fun _ => h) (fun _ => h) xi zeta
      (fun _ => sourceOriginalB26SmallTupleD434 SP sm J ell d)
      (fun _ => theta) (fun _ => o) k sigma tau epsSrc epsTgt
      (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ p => p.val)
        J ell sizes prime q data.Vsmall tt f d))


/-- Exact SMALL endpoint lifting of the comparison-minus-ban identity. -/
theorem source_original_B26_NODUP_MARKED_SMALL_CLEAN_RAW_DECOMPOSITION434
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
    sourceOriginalB26NodupMarkedSmallCleanRaw434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f =
    fun xs a S r =>
      sourceOriginalB26NodupMarkedSmallComparison434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r -
      sourceOriginalB26NodupMarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r := by
  funext xs a S r
  simp only [sourceOriginalB26NodupMarkedSmallCleanRaw434,sourceOriginalB26NodupMarkedSmallComparison434,
    sourceOriginalB26NodupMarkedSmallAuxBan434,sourceOriginalMarkedSmallSynthesis434,
    sourceOriginalSmallEndpointSynthesis434,
    source_original_B26_NODUP_NUMERIC_RESIDUE_CLEAN_RAW_DECOMPOSITION434,mul_sub]

/-- The true ban correction has arbitrary-power energy saving after both
SMALL maps. The slot bound remains explicit; no history count or bounded
future is assumed, and the original physical tilted density is unchanged. -/
theorem eventually_source_original_B26_NODUP_MARKED_SMALL_AUX_BAN434
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
      (sourceOriginalB26NodupMarkedSmallAuxBan434 data SP sm sizes prime q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ p => p.val)
      J ell sizes prime mu f := by
  let Cs := sourceOriginalB26SmallNormExponent434 ell q cfg.vmin cfg.C0
  let Bideal := Bgoal+2*Cs
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_NODUP_PHYSICAL_NUMERIC_RESIDUE_AUX_BAN434
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
    sourceOriginalB26NodupNumericResidueAuxBanFamily434 data SP sm sizes prime q N blockA blockB
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

