module

public import Green64.Library.Analysis.Estimates.Part013

@[expose] public section

/-!
# Weights / B26TiltedAveragedAuxBan

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26TiltedAveragedAuxBan -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Actual auxiliary/ACTIVE ban correction in the full physical tilted bilinear
pairing, coherently summed over the genuine family and both normalized
BIG permutation averages. The logarithmic saving is proved from the
exponential prime floor and the actual canonical K bound. -/
theorem eventually_source_original_B26_TILTED_AVERAGED_AUX_BAN434
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
      (Q : ℕ) (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (epsSrc epsTgt : Bool) (dsmall : ℕ)
      (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    ‖sourceOriginalB26TiltedCanonicalAuxBanForm434 data q (2*Nat.ceil (L^(0.52:ℝ))) blockA blockB
      J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall u v‖^2 ≤
      L^(-Bgoal)*sourceOriginalB26ActiveEnergy434 BP J ell mu u*
        sourceOriginalB26ActiveEnergy434 BP J ell mu v := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  let Ct := sourceOriginalB26TiltDensityExponent434 ell cfg.tmax cfg.C0
  let Dper : ℝ := Bgoal/2+E+Ct
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_canonical_aux_ban_saving434
    cfg.cexp cfg.vmin ((cfg.tmax:ℝ)*cfg.C0) Cslots Dper Cq Cxi
    hc cfg.hv (mul_nonneg (Nat.cast_nonneg _) cfg.hC0),
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc,
    eventually_ge_atTop (1:ℝ)] with L hSave hVisit hL
  intro ι G instI instDI instG instDG x Y Hprime data instNZ q hq hq1
    hVbig hTbLower blockA blockB hBlocks J m hmJ hm hSlots
    Q h xi hh hxi hQ hXi ζ theta o k ho epsSrc epsTgt dsmall u v
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val) q N g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 N g p (hVisit p.val (hTbLower g p.val p.property))).1
  have hb0 (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val) q N g p := by
    have hh := hb g p
    linarith only [hh]
  let muH := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let Active := (g : G) → Fin (J+ell) → BP g
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  let EU := sourceOriginalB26ActiveEnergy434 BP J ell mu u
  let EV := sourceOriginalB26ActiveEnergy434 BP J ell mu v
  let delta := L^(-Dper)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVEq (g : G) : data.Vbig g = ∑ p : BP g,1/(p.val:ℝ) := by
    rw [hVbig]
    simpa [BP] using (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).symm
  obtain ⟨hmuNN,hmuMass⟩ := source_original_joint_harmonic_normalized434
    BP (fun _ p => p.val) data.Vbig hVpos hVEq
  have hmuH (g : G) (p : BP g) : 0 < muH g p := by
    have hp : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast (data.hTbPrime g p.val p.property).pos
    exact div_pos (one_div_pos.mpr hp) (hVpos g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    exact one_div_pos.mpr (mul_pos (mul_pos (hVpos g)
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb0 g p))
  have hEU : 0 ≤ EU := source_original_B26_active_energy_nonneg434 BP J ell mu hmu u
  have hEV : 0 ≤ EV := source_original_B26_active_energy_nonneg434 BP J ell mu hmu v
  have hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hb : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hb : ((blockA.card+blockB.card:ℕ):ℝ) ≤ (Fintype.card G:ℝ)).trans
      data.hBigGroups
  have hPattern (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ((ν.1.card+ν.2.card:ℕ):ℝ) ≤ ((cfg.tmax:ℝ)*cfg.C0)*Real.log L := by
    have hmem := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
    have hNA : ν.1.card ≤ blockA.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.1
    have hNB : ν.2.card ≤ blockB.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.2.2
    have hNat : ν.1.card+ν.2.card ≤ m*(blockA.card+blockB.card) := by nlinarith only [hNA,hNB]
    calc
      _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
      _ ≤ (m:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
      _ ≤ (cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm)
          (mul_nonneg cfg.hC0 (Real.log_nonneg hL))
      _ = _ := by ring
  have hPer (sigma tau : BigGroupPerm (BG := G) (J+ell))
      (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ‖sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi ζ (fun _ => dsmall)
        (fun _ => theta) (fun _ => o) k (fun _ => sigma) (fun _ => tau)
        (fun _ => u) (fun _ => v) ν‖^2 ≤ (delta^2*(L^Ct)^2)*EU*EV := by
    apply source_original_B26_physical_tilt_uniform_bilinear434
      BP (fun _ p => p.val) q N data.Vbig hVpos hVEq hb
      J ell m cfg.tmax hmJ hm ν sigma tau cfg.C0 L hL data.hBigGroups
      delta hdelta u v
    intro s t
    exact hSave data.Tb data.Vbig J ell m hmJ ν
      (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m ν hν)
      Q h h xi hh hh hxi hVbig data.hVbig hTbLower (hPattern ν hν)
      hSlots hQ hXi dsmall s t sigma tau ζ theta o k ho
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0)
      (Real.log_nonneg (by norm_num))
  have hCard : (family.card:ℝ) ≤ L^E :=
    (source_original_probe_family_log_power_card434 blockA blockB m L cfg.C0 hL hGroups).trans
      (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hBudget : (family.card:ℝ)^2*(delta^2*(L^Ct)^2) ≤ L^(-Bgoal) := by
    calc
      _ ≤ (L^E)^2*((L^(-Dper))^2*(L^Ct)^2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hCard 2)
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = L^(-Bgoal) := by
        rw [← Real.rpow_two,← Real.rpow_two,← Real.rpow_two,
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,
          ← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        dsimp [Dper]
        ring
  let z := fun (sigma tau : BigGroupPerm (BG := G) (J+ell)) =>
    ∑ ν ∈ family,sign ν * sourceOriginalB26TiltedPermutedAuxBanPairing434
      data q N J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν
  have hz (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
      ‖z sigma tau‖^2 ≤ L^(-Bgoal)*EU*EV := by
    have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
        ‖sign ν * sourceOriginalB26TiltedPermutedAuxBanPairing434
          data q N J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
          (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
          (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν‖^2 ≤
        (1:ℝ)^2*((delta^2*(L^Ct)^2)*EU*EV) := by
      have hs : ‖sign ν‖=1 := by
        dsimp only [sign]
        rw [norm_mul]
        split_ifs <;> simp
      rw [norm_mul,hs,one_mul,one_pow,one_mul]
      exact hPer sigma tau ν hν
    have hs := source_original_true_finite_weighted_minor_square434
      family
      (fun ν => sign ν * sourceOriginalB26TiltedPermutedAuxBanPairing434
        data q N J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
        (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
        (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν)
      (fun _ => (1:ℝ)) ((delta^2*(L^Ct)^2)*EU*EV)
      (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg delta) (sq_nonneg _)) hEU) hEV)
      (by intro ν hν;norm_num) hEach
    have hs' : ‖z sigma tau‖^2 ≤ (family.card:ℝ)^2*((delta^2*(L^Ct)^2)*EU*EV) := by
      simpa only [z,Finset.sum_const,nsmul_eq_mul,mul_one] using hs
    calc
      _ ≤ (family.card:ℝ)^2*((delta^2*(L^Ct)^2)*EU*EV) := hs'
      _ = ((family.card:ℝ)^2*(delta^2*(L^Ct)^2))*(EU*EV) := by ring
      _ ≤ L^(-Bgoal)*(EU*EV) := mul_le_mul_of_nonneg_right hBudget (mul_nonneg hEU hEV)
      _ = _ := by ring
  exact source_original_B26_big_permutation_mean_square434 (J+ell) z
    (L^(-Bgoal)) EU EV (Real.rpow_nonneg hLp.le _) hEU hEV hz
end Green64Analytic.CorrelationSquare

end

