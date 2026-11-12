module

public import Green64.Library.Weights.Part107
public import Green64.Library.Sieve.Foundations.Part001

@[expose] public section

/-!
# Weights / Part108

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Terminal001 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoTerminalScales.lean; original line 8. -/
noncomputable def sourceEchiJConstant : ℝ := (1+Real.log 4)/Real.log 2+1



/- Exact source owner: SourceShiftTwoLargeConductorSums.lean; original line 26. -/
noncomputable def sourceEchiLargeScalarBudget (r₀ : ℕ) (Ψ : ℝ → ℝ)
    (L : ℝ) (K T : ℕ) : ℝ :=
  L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ *
    (8*(2:ℝ)^T*Real.exp (L/2) +
      12*Real.sqrt Real.pi*(T:ℝ)*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) +
      4*Real.pi*Real.exp L/(2:ℝ)^K)

/- All large conductor dyads of each actual box summed, with exact geometric
costs rather than a loss from counting all moduli. -/



/- Exact source owner: SourceShiftTwoSmallScalarBudget.lean; original line 7. -/
noncomputable def sourceEchiSmallScalarBudget (r₀ : ℕ) (L C A θ B S V : ℝ) : ℝ :=
  L^C * L^sourceDeletedCoefficientExponent *
    (2*Real.exp L*B*L^(-A)*V +
      4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L)*(θ/sourceOriginalQ0Scale r₀)*S)

/- Uniform source-box small budget with all true scales estimated.
The deleted-prime mask cost gains exp(-αL), with α the literal Q0 scale. -/



/- Exact source owner: SourceShiftTwoTerminalScales.lean; original line 9. -/
noncomputable def sourceEchiTConstant (θ : ℝ) : ℝ := θ/Real.log 2+1



/- Exact source owner: SourceShiftTwoTerminalBudget.lean; original line 16. -/
noncomputable def sourceEchiTerminalConstant (r₀ : ℕ) (Ψ : ℝ → ℝ)
    (θ B S V : ℝ) : ℝ :=
  2*B*V+4*(θ/sourceOriginalQ0Scale r₀)*S+
    sourceLogMellinMass Ψ*(16+12*Real.sqrt Real.pi*sourceEchiTConstant θ+4*Real.pi)

/- Uniform terminal scalar bound after the actual conductor scales are selected.
Every saving comes from SW, Q0 size, or the proved large sieve. -/



/- Exact source owner: SourceShiftTwoLargeScalarGeometry.lean; original line 7. -/
theorem source_echi_alpha_bounds (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    0 < sourceOriginalQ0Scale r₀ ∧
      (11/5:ℝ)*sourceOriginalQ0Scale r₀ ≤ 1 := by
  have hr : (1:ℝ) ≤ r₀ := by exact_mod_cast hr₀
  unfold sourceOriginalQ0Scale
  constructor
  · positivity
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 11*r₀)).mpr
    nlinarith

/- Uniform power saving in each genuine source large-conductor box.
This is a consequence of the literal Q0 endpoints, not a balanced-box premise. -/



/- Exact source owner: SourceShiftTwoTerminalBudget.lean; original line 8. -/
theorem source_echi_coefficient_exponent_pos : 0 < sourceDeletedCoefficientExponent := by
  unfold sourceDeletedCoefficientExponent
  apply mul_pos
  · have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · apply Real.log_pos
    exact lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _)



/- Exact source owner: SourceShiftTwoTerminalAbsorption.lean; original line 7. -/
theorem source_echi_exp_rpow_absorb :
    ∀ (η m n : ℝ), 0 < η → ∀ᶠ L : ℝ in Filter.atTop,
      Real.exp ((1-η)*L)*L^m ≤ Real.exp L*L^n := by
  intro η m n hη
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m-n) η hη
  have hb := ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hb,Filter.eventually_gt_atTop (0:ℝ)] with L hb hL
  have he : (L^(m-n)*Real.exp (-η*L))*(Real.exp L*L^n) =
      Real.exp ((1-η)*L)*L^m := by
    calc
      _ = (Real.exp (-η*L)*Real.exp L)*(L^(m-n)*L^n) := by ring
      _ = _ := by
        rw [← Real.rpow_add hL,← Real.exp_add]
        congr 1 <;> ring
  rw [← he]
  exact mul_le_of_le_one_left (by positivity) hb



/- Exact source owner: SourceShiftTwoTerminalBudget.lean; original line 23. -/
theorem source_echi_terminal_budget_eventually (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (θ D B S V : ℝ) (hθ : 0 < θ) (hθu : θ < 1/2)
    (hD : 0 < D) (hB : 0 ≤ B) (hS : 0 ≤ S) (hV : 0 ≤ V) :
    let k := sourceDeletedCoefficientExponent+D+2
    let C := k+1
    let A := C+sourceDeletedCoefficientExponent+D+2
    ∀ᶠ L : ℝ in atTop, ∀ K T : ℕ,
      L^k ≤ (2:ℝ)^K → (2:ℝ)^T ≤ 2*Real.exp (θ*L) →
      (T:ℝ) ≤ sourceEchiTConstant θ*L →
      sourceEchiSmallScalarBudget r₀ L C A θ B S V+
        sourceEchiLargeScalarBudget r₀ Ψ L K T ≤
      sourceEchiTerminalConstant r₀ Ψ θ B S V*Real.exp L*L^(-D-2) := by
  dsimp only
  obtain ⟨hα,_⟩ := source_echi_alpha_bounds r₀ hr₀
  have hb1 := source_echi_exp_rpow_absorb (sourceOriginalQ0Scale r₀)
    (sourceDeletedCoefficientExponent+D+2+1+sourceDeletedCoefficientExponent) (-D-2) hα
  have hb2 := source_echi_exp_rpow_absorb (1/2-θ)
    sourceDeletedCoefficientExponent (-D-2) (by linarith)
  have hb3 := source_echi_exp_rpow_absorb (sourceOriginalQ0Scale r₀/2)
    (sourceDeletedCoefficientExponent+1) (-D-2) (by positivity)
  filter_upwards [hb1,hb2,hb3,eventually_ge_atTop (2:ℝ)] with L hb1 hb2 hb3 hL
  have hL0 : 0 < L := by linarith
  have hm : 0 ≤ sourceLogMellinMass Ψ := source_log_mellin_mass_nonneg Ψ
  have hT0 : 0 ≤ sourceEchiTConstant θ := by
    unfold sourceEchiTConstant
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro K T hK hT hTc
  let E : ℝ := Real.exp L*L^(-D-2)
  have hfirstSmall :
      L^(sourceDeletedCoefficientExponent+D+2+1)*L^sourceDeletedCoefficientExponent*
        (2*Real.exp L*B*L^(-(sourceDeletedCoefficientExponent+D+2+1+sourceDeletedCoefficientExponent+D+2))*V) =
      2*B*V*E := by
    dsimp [E]
    calc
      _ = 2*B*V*Real.exp L*
        (L^(sourceDeletedCoefficientExponent+D+2+1)*L^sourceDeletedCoefficientExponent*
          L^(-(sourceDeletedCoefficientExponent+D+2+1+sourceDeletedCoefficientExponent+D+2))) := by ring
      _ = _ := by rw [← Real.rpow_add hL0,← Real.rpow_add hL0]; ring_nf
  have hmaskSmall :
      L^(sourceDeletedCoefficientExponent+D+2+1)*L^sourceDeletedCoefficientExponent*
        (4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L)*(θ/sourceOriginalQ0Scale r₀)*S) ≤
      4*(θ/sourceOriginalQ0Scale r₀)*S*E := by
    have hh := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ 4*(θ/sourceOriginalQ0Scale r₀)*S)
    dsimp [E]
    rw [Real.rpow_add hL0] at hh
    nlinarith
  have hsmall : sourceEchiSmallScalarBudget r₀ L
      (sourceDeletedCoefficientExponent+D+2+1)
      (sourceDeletedCoefficientExponent+D+2+1+sourceDeletedCoefficientExponent+D+2) θ B S V ≤
      (2*B*V+4*(θ/sourceOriginalQ0Scale r₀)*S)*E := by
    unfold sourceEchiSmallScalarBudget
    rw [mul_add,hfirstSmall]
    nlinarith
  have hlarge1 : L^sourceDeletedCoefficientExponent*
      (8*(2:ℝ)^T*Real.exp (L/2)) ≤ 16*E := by
    have hh := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 8*L^sourceDeletedCoefficientExponent*Real.exp (L/2))
    have he : Real.exp (θ*L)*Real.exp (L/2) = Real.exp ((1-(1/2-θ))*L) := by
      rw [← Real.exp_add]; congr 1; ring
    have hb := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 16)
    dsimp [E]
    rw [← he] at hb
    nlinarith
  have hlarge2 : L^sourceDeletedCoefficientExponent*
      (12*Real.sqrt Real.pi*(T:ℝ)*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L)) ≤
      12*Real.sqrt Real.pi*sourceEchiTConstant θ*E := by
    have hh := mul_le_mul_of_nonneg_left hTc (by positivity : 0 ≤ L^sourceDeletedCoefficientExponent*12*Real.sqrt Real.pi*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L))
    have hb := mul_le_mul_of_nonneg_left hb3 (by positivity : 0 ≤ 12*Real.sqrt Real.pi*sourceEchiTConstant θ)
    rw [Real.rpow_add hL0,Real.rpow_one] at hb
    dsimp [E]
    nlinarith
  have hlarge3 : L^sourceDeletedCoefficientExponent*
      (4*Real.pi*Real.exp L/(2:ℝ)^K) ≤ 4*Real.pi*E := by
    have hd := div_le_div_of_nonneg_left (by positivity : 0 ≤ L^sourceDeletedCoefficientExponent*4*Real.pi*Real.exp L)
      (Real.rpow_pos_of_pos hL0 _) hK
    have he : L^sourceDeletedCoefficientExponent*
        (4*Real.pi*Real.exp L/L^(sourceDeletedCoefficientExponent+D+2)) = 4*Real.pi*E := by
      dsimp [E]
      rw [div_eq_mul_inv,← Real.rpow_neg hL0.le]
      calc
        _ = 4*Real.pi*Real.exp L*(L^sourceDeletedCoefficientExponent*L^(-(sourceDeletedCoefficientExponent+D+2))) := by ring
        _ = _ := by rw [← Real.rpow_add hL0]; ring_nf
    calc
      _ = (L^sourceDeletedCoefficientExponent*4*Real.pi*Real.exp L)/(2:ℝ)^K := by ring
      _ ≤ _ := hd
      _ = L^sourceDeletedCoefficientExponent*(4*Real.pi*Real.exp L/L^(sourceDeletedCoefficientExponent+D+2)) := by ring
      _ = _ := he
  have hlarge : sourceEchiLargeScalarBudget r₀ Ψ L K T ≤
      sourceLogMellinMass Ψ*(16+12*Real.sqrt Real.pi*sourceEchiTConstant θ+4*Real.pi)*E := by
    unfold sourceEchiLargeScalarBudget
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hlarge1 hlarge2) hlarge3) hm
    nlinarith
  unfold sourceEchiTerminalConstant
  dsimp [E] at hsmall hlarge
  nlinarith



/- Exact source owner: SourceShiftTwoDyadicQuantitativeCover.lean; original line 9. -/
theorem source_echi_exp_dyadic_cover (t : ℝ) (ht : 0 ≤ t) :
    let N := ⌈t/Real.log 2⌉₊
    Real.exp t ≤ (2:ℝ)^N ∧ (2:ℝ)^N ≤ 2*Real.exp t ∧
      (N:ℝ) ≤ t/Real.log 2+1 := by
  dsimp only
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnon : 0 ≤ t/Real.log 2 := div_nonneg ht hl.le
  have hlow := Nat.le_ceil (t/Real.log 2)
  have hhigh := (Nat.ceil_lt_add_one hnon).le
  have hexp (n : ℕ) : (2:ℝ)^n = Real.exp ((n:ℝ)*Real.log 2) := by
    rw [← Real.log_pow,Real.exp_log (by positivity)]
  refine ⟨?_,?_,hhigh⟩
  · rw [hexp]
    apply Real.exp_le_exp.mpr
    exact (div_le_iff₀ hl).mp hlow
  · rw [hexp,show 2*Real.exp t = Real.exp (Real.log 2+t) by rw [Real.exp_add,Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hhigh hl.le
    have hcancel : t/Real.log 2*Real.log 2 = t := div_mul_cancel₀ t (ne_of_gt hl)
    nlinarith

/- Explicit source cutoff cover has J=O(L), and hence at most O(L)
actual prime/residual boxes. This controls the real product cutoff as stated. -/



/- Exact source owner: SourceShiftTwoSourceBoxCount.lean; original line 9. -/
theorem source_echi_compatible_log_window (L : ℝ) (j k : ℕ)
    (hc : sourceEchiCompatible L j k) :
    L < ((j:ℝ)+(k:ℝ)+2)*Real.log 2 ∧
    ((j:ℝ)+(k:ℝ))*Real.log 2 ≤ L+Real.log 2 := by
  have h1 := Real.log_lt_log (Real.exp_pos L) hc.1
  have h2 := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^j*(2:ℝ)^k) hc.2
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    have hh := Real.log_pow (2:ℝ) 2
    norm_num at hh
    exact hh
  -- Explicit rewrites keep all logarithm nonzero obligations visible.
  have h1' : L < 2*Real.log 2 + (j:ℝ)*Real.log 2 + (k:ℝ)*Real.log 2 := by
    simpa only [Real.log_exp,Real.log_mul (by positivity : (4*(2:ℝ)^j)≠0)
      (by positivity : (2:ℝ)^k≠0),
      Real.log_mul (by norm_num : (4:ℝ)≠0) (by positivity : (2:ℝ)^j≠0),
      Real.log_pow,h4] using h1
  have h2' : (j:ℝ)*Real.log 2 + (k:ℝ)*Real.log 2 ≤ Real.log 2+L := by
    simpa only [Real.log_mul (by positivity : (2:ℝ)^j≠0) (by positivity : (2:ℝ)^k≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt (Real.exp_pos L)),
      Real.log_exp,Real.log_pow] using h2
  constructor <;> nlinarith



/- Exact source owner: SourceShiftTwoSourceBoxCount.lean; original line 31. -/
theorem source_echi_compatible_indices_close (L : ℝ) (j k k' : ℕ)
    (hk : sourceEchiCompatible L j k) (hk' : sourceEchiCompatible L j k') :
    k < k'+3 ∧ k' < k+3 := by
  have h := source_echi_compatible_log_window L j k hk
  have h' := source_echi_compatible_log_window L j k' hk'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkk : (k:ℝ) < (k':ℝ)+3 := by nlinarith
  have hkk' : (k':ℝ) < (k:ℝ)+3 := by nlinarith
  constructor
  · exact_mod_cast hkk
  · exact_mod_cast hkk'

/- At most three compatible residual dyads for each prime dyad.
The injection (j,k) ↦ (j,k mod 3) makes the finite count explicit. -/



/- Exact source owner: SourceShiftTwoSourceBoxCount.lean; original line 45. -/
theorem source_original_source_boxes_card (r₀ : ℕ) (L : ℝ) (J : ℕ) :
    (sourceEchiSourceBoxes r₀ L J).card ≤ 3*J := by
  have hh : (sourceEchiSourceBoxes r₀ L J).card ≤
      ((Finset.range J) ×ˢ (Finset.range 3)).card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ×ℕ => (a.1,a.2%3))
    · intro a ha
      have hm := Finset.mem_filter.mp ha
      have hj := (Finset.mem_product.mp hm.1).1
      exact Finset.mem_product.mpr ⟨hj,Finset.mem_range.mpr (Nat.mod_lt _ (by omega))⟩
    · intro a ha b hb he
      change (a.1,a.2%3) = (b.1,b.2%3) at he
      have hj : a.1 = b.1 := (Prod.mk.inj he).1
      have hk : a.2%3 = b.2%3 := (Prod.mk.inj he).2
      have hc := (Finset.mem_filter.mp ha).2.2
      have hc' := (Finset.mem_filter.mp hb).2.2
      rw [← hj] at hc'
      have hclose := source_echi_compatible_indices_close L a.1 a.2 b.2 hc hc'
      have heq : a.2 = b.2 := by omega
      exact Prod.ext hj heq
  simpa only [Finset.card_product,Finset.card_range,mul_comm] using hh



/- Exact source owner: SourceShiftTwoDyadicQuantitativeCover.lean; original line 32. -/
theorem source_original_quantitative_source_cover (r₀ : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ J : ℕ, ⌊2*Real.exp L⌋₊ ≤ 2^J-1 ∧
      (J:ℝ) ≤ (L+Real.log 4)/Real.log 2+1 ∧
      ((sourceEchiSourceBoxes r₀ L J).card:ℝ) ≤
        3*((L+Real.log 4)/Real.log 2+1) := by
  let J := ⌈(L+Real.log 4)/Real.log 2⌉₊
  have ht : 0 ≤ L+Real.log 4 := add_nonneg hL (Real.log_nonneg (by norm_num))
  have hh := source_echi_exp_dyadic_cover (L+Real.log 4) ht
  dsimp only at hh
  have he : Real.exp (L+Real.log 4) = 4*Real.exp L := by
    rw [Real.exp_add,Real.exp_log (by norm_num)]; ring
  have hexp : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hfloor : (⌊2*Real.exp L⌋₊:ℝ) ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hcast : (⌊2*Real.exp L⌋₊:ℝ)+1 ≤ ((2^J:ℕ):ℝ) := by
    have hpow : 4*Real.exp L ≤ (2:ℝ)^J := by simpa only [he,J] using hh.1
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    nlinarith
  have hnat : ⌊2*Real.exp L⌋₊+1 ≤ 2^J := by exact_mod_cast hcast
  have hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1 := by omega
  have hJ : (J:ℝ) ≤ (L+Real.log 4)/Real.log 2+1 := hh.2.2
  refine ⟨J,hN,hJ,?_⟩
  have hcard : ((sourceEchiSourceBoxes r₀ L J).card:ℝ) ≤ 3*(J:ℝ) := by
    exact_mod_cast source_original_source_boxes_card r₀ L J
  exact hcard.trans (mul_le_mul_of_nonneg_left hJ (by norm_num))



/- Exact source owner: SourceShiftTwoTerminalScales.lean; original line 11. -/
theorem source_echi_terminal_scales (r₀ : ℕ) (k θ : ℝ) (hk : 0 < k) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop, ∃ J K T : ℕ,
      K ≤ T ∧ ⌊(Real.exp L)^θ⌋₊ ≤ 2^T ∧
      ⌊2*Real.exp L⌋₊ ≤ 2^J-1 ∧
      L^k ≤ (2:ℝ)^K ∧ (2:ℝ)^K ≤ L^(k+1) ∧
      (2:ℝ)^T ≤ 2*Real.exp (θ*L) ∧
      (J:ℝ) ≤ sourceEchiJConstant*L ∧
      (T:ℝ) ≤ sourceEchiTConstant θ*L := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s:=1) 1 (by norm_num : (0:ℝ)<1)).bound (div_pos hθ hk)
  filter_upwards [hsmall,eventually_ge_atTop (2:ℝ)] with L hs hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  simp only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg hL0.le] at hs
  have hklog : k*Real.log L ≤ θ*L := by
    have hh := mul_le_mul_of_nonneg_left hs hk.le
    field_simp at hh
    nlinarith
  let K := ⌈(k*Real.log L)/Real.log 2⌉₊
  let T := ⌈(θ*L)/Real.log 2⌉₊
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKT : K ≤ T := Nat.ceil_mono ((div_le_div_iff_of_pos_right hl2).mpr hklog)
  have hcoverK := source_echi_exp_dyadic_cover (k*Real.log L) (mul_nonneg hk.le hlog)
  have hcoverT := source_echi_exp_dyadic_cover (θ*L) (mul_nonneg hθ.le hL0.le)
  have hek : Real.exp (k*Real.log L) = L^k := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring
  change Real.exp (k*Real.log L) ≤ (2:ℝ)^K ∧ (2:ℝ)^K ≤ 2*Real.exp (k*Real.log L) ∧
    (K:ℝ) ≤ (k*Real.log L)/Real.log 2+1 at hcoverK
  rw [hek] at hcoverK
  change Real.exp (θ*L) ≤ (2:ℝ)^T ∧ (2:ℝ)^T ≤ 2*Real.exp (θ*L) ∧
    (T:ℝ) ≤ (θ*L)/Real.log 2+1 at hcoverT
  have hcutK : (2:ℝ)^K ≤ L^(k+1) := by
    calc
      _ ≤ 2*L^k := hcoverK.2.1
      _ ≤ L*L^k := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hQcast : (⌊(Real.exp L)^θ⌋₊:ℝ) ≤ (2:ℝ)^T := by
    have hh := Nat.floor_le (Real.rpow_nonneg (Real.exp_pos L).le θ)
    have he : (Real.exp L)^θ = Real.exp (θ*L) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]; congr 1; ring
    rw [he] at hh ⊢
    exact hh.trans hcoverT.1
  have hQ : ⌊(Real.exp L)^θ⌋₊ ≤ 2^T := by exact_mod_cast hQcast
  obtain ⟨J,hN,hJ,_⟩ := source_original_quantitative_source_cover r₀ L hL0.le
  have hJ' : (J:ℝ) ≤ sourceEchiJConstant*L := by
    unfold sourceEchiJConstant
    apply hJ.trans
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ ((1+Real.log 4)*L)/Real.log 2+L :=
        add_le_add ((div_le_div_iff_of_pos_right hl2).mpr (by nlinarith)) (by linarith)
      _ = _ := by ring
  have hT' : (T:ℝ) ≤ sourceEchiTConstant θ*L := by
    apply hcoverT.2.2.trans
    unfold sourceEchiTConstant
    field_simp
    nlinarith
  exact ⟨J,K,T,hKT,hQ,hN,hcoverK.1,hcutK,hcoverT.2.1,hJ',hT'⟩



/- Exact source owner: SourceShiftTwoSourceBoxRanges.lean; original line 9. -/
theorem source_original_box_scale_ranges
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (J : ℕ) (a : ℕ×ℕ)
    (ha : a ∈ sourceEchiSourceBoxes r₀ L J) :
    Real.exp (sourceOriginalQ0Scale r₀*L) < 2*(2:ℝ)^a.1 ∧
    (2:ℝ)^a.1 ≤ Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) ∧
    Real.exp ((1-(6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) < 4*(2:ℝ)^a.2 ∧
    (2:ℝ)^a.2 ≤ 4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L) ∧
    (2:ℝ)^a.1*(2:ℝ)^a.2 ≤ 2*Real.exp L := by
  obtain ⟨hm,⟨⟨p,hp⟩,hc⟩⟩ := Finset.mem_filter.mp ha
  obtain ⟨hpd,hpQ⟩ := Finset.mem_filter.mp hp
  have hpr := source_original_Q_actual_prime_range r₀ _ L hr₀ _ p hpQ
  rw [source_original_P_scale_zero_eq_Q0 r₀ L hr₀] at hpr
  have hdy := (source_echi_dyad_mem a.1 p).mp hpd
  have hpl : (2:ℝ)^a.1 ≤ (p:ℝ) := by exact_mod_cast hdy.1
  have hpu : (p:ℝ) < 2*(2:ℝ)^a.1 := by
    have h : (p:ℝ) < (2:ℝ)^(a.1+1) := by exact_mod_cast hdy.2
    simpa only [pow_succ,mul_comm] using h
  have hp0 : 0 < (2:ℝ)^a.1 := by positivity
  have hu0 : 0 < (2:ℝ)^a.2 := by positivity
  have hlo : Real.exp (sourceOriginalQ0Scale r₀*L) < 2*(2:ℝ)^a.1 :=
    hpr.1.trans_lt hpu
  have hhi : (2:ℝ)^a.1 ≤ Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) := by
    exact hpl.trans (by simpa only [mul_assoc] using hpr.2)
  have he1 : Real.exp L =
      Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) *
        Real.exp ((1-(6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp L = Real.exp (sourceOriginalQ0Scale r₀*L) *
      Real.exp ((1-sourceOriginalQ0Scale r₀)*L) := by
    rw [← Real.exp_add]; congr 1; ring
  have huLow : Real.exp ((1-(6/5:ℝ)*sourceOriginalQ0Scale r₀)*L) <
      4*(2:ℝ)^a.2 := by
    have hx := hc.1
    have hh := mul_le_mul_of_nonneg_right hhi hu0.le
    rw [he1] at hx
    nlinarith [Real.exp_pos (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L)]
  have huHigh : (2:ℝ)^a.2 ≤ 4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L) := by
    have hx := hc.2
    have hh := mul_lt_mul_of_pos_right hlo hu0
    rw [he2] at hx
    nlinarith [Real.exp_pos (sourceOriginalQ0Scale r₀*L)]
  exact ⟨hlo,hhi,huLow,huHigh,hc.2⟩

/- Actual Q0 lower logarithmic scale, needed for polynomial conductor SW. -/



/- Exact source owner: SourceShiftTwoSourceBoxRanges.lean; original line 53. -/
theorem source_original_box_prime_log_lower
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (J : ℕ) (a : ℕ×ℕ)
    (ha : a ∈ sourceEchiSourceBoxes r₀ L J) :
    sourceOriginalQ0Scale r₀*L-Real.log 2 < Real.log ((2:ℝ)^a.1) := by
  have hr := (source_original_box_scale_ranges r₀ hr₀ L J a ha).1
  have hh := Real.log_lt_log (Real.exp_pos _) hr
  rw [Real.log_exp,Real.log_mul (by norm_num) (by positivity)] at hh
  linarith



/- Exact source owner: SourceShiftTwoSWMatchedDyads.lean; original line 10. -/
theorem source_original_box_log_and_cutoff_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (C : ℝ) (hC : 0 < C) (Y : ℝ) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧
      ∀ (J : ℕ) (a : ℕ×ℕ), a ∈ sourceEchiSourceBoxes r₀ L J →
        Y ≤ (2:ℝ)^a.1 ∧
        (sourceOriginalQ0Scale r₀/2)*L ≤ Real.log ((2:ℝ)^a.1) ∧
        L^C ≤ (Real.log ((2:ℝ)^a.1))^(C+1) := by
  let c : ℝ := sourceOriginalQ0Scale r₀/2
  have hr : (0:ℝ) < r₀ := by exact_mod_cast hr₀
  have hc : 0 < c := by dsimp [c,sourceOriginalQ0Scale]; positivity
  have hcPow : 0 < c^(C+1) := Real.rpow_pos_of_pos hc _
  let Y' : ℝ := max Y 1
  have hY' : 0 < Y' := (by norm_num : (0:ℝ)<1).trans_le (le_max_right _ _)
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_ge_atTop (Real.log 2/c),
    eventually_ge_atTop (Real.log Y'/c),
    eventually_ge_atTop (1/(c^(C+1)))] with L hL hlog hY hpow
  refine ⟨hL,?_⟩
  intro J a ha
  have hpl := source_original_box_prime_log_lower r₀ hr₀ L J a ha
  have hclog : Real.log 2 ≤ c*L := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlog
  have hlower : c*L ≤ Real.log ((2:ℝ)^a.1) := by
    have he : sourceOriginalQ0Scale r₀ = 2*c := by dsimp [c]; ring
    rw [he] at hpl
    nlinarith
  have hYlog : Real.log Y' ≤ c*L := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hY
  have hYP : Y ≤ (2:ℝ)^a.1 := by
    apply (le_max_left Y 1).trans
    have hh := Real.exp_le_exp.mpr (hYlog.trans hlower)
    simpa only [Real.exp_log hY',Real.exp_log (by positivity : (0:ℝ)<(2:ℝ)^a.1)] using hh
  have hpow1 : 1 ≤ c^(C+1)*L := by
    have hh := (div_le_iff₀ hcPow).mp hpow
    nlinarith
  have hscale : L^C ≤ (c*L)^(C+1) := by
    rw [Real.mul_rpow hc.le hL.le, Real.rpow_add hL C 1, Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_right hpow1 (Real.rpow_nonneg hL.le C)
    nlinarith
  exact ⟨hYP,hlower,hscale.trans
    (Real.rpow_le_rpow (by positivity) hlower (by linarith))⟩

/- OPEN SW now gives literal source Q0 prefixes on every genuine box
for all f<=L^C. Constants depend only on fixed r₀,C,A. -/



/- Exact source owner: SourceShiftTwoSWMatchedDyads.lean; original line 52. -/
theorem source_SW_original_matched_prefixes
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (C A : ℝ) (hC : 0 < C) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J : ℕ) (a : ℕ×ℕ), a ∈ sourceEchiSourceBoxes r₀ L J →
        ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
          χ.IsPrimitive → χ ≠ 1 → (f:ℝ) ≤ L^C →
            ∀ n, n ≤ 2^a.1 →
              ‖∑ p ∈ Finset.Ioc (sourceEchiDyadLower a.1)
                  (sourceEchiDyadLower a.1+n),
                if p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
                  (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
                then χ p else 0‖ ≤ B*(2:ℝ)^a.1*L^(-A) := by
  obtain ⟨B,Y,hB,hbound⟩ := source_SW_original_Q0_prefixes hSW (C+1) A (by linarith) hA
  let c : ℝ := sourceOriginalQ0Scale r₀/2
  have hr : (0:ℝ)< r₀ := by exact_mod_cast hr₀
  have hc : 0 < c := by dsimp [c,sourceOriginalQ0Scale]; positivity
  refine ⟨B*c^(-A),mul_nonneg hB (Real.rpow_nonneg hc.le _),?_⟩
  filter_upwards [source_original_box_log_and_cutoff_eventually r₀ hr₀ C hC Y] with L hgeom
  intro J a ha f inst χ hprim hnon hf n hn
  obtain ⟨hYP,hlog,hcut⟩ := hgeom.2 J a ha
  have hh := hbound r₀ L a.1 f χ hYP hprim hnon (hf.trans hcut) n hn
  have hneg : (Real.log ((2:ℝ)^a.1))^(-A) ≤ c^(-A)*L^(-A) := by
    have ht := Real.rpow_le_rpow_of_nonpos (mul_pos hc hgeom.1) hlog (by linarith : -A ≤ 0)
    simpa only [Real.mul_rpow hc.le hgeom.1.le] using ht
  have hm := mul_le_mul_of_nonneg_left hneg (mul_nonneg hB (by positivity : (0:ℝ)≤(2:ℝ)^a.1))
  apply hh.trans
  convert hm using 1 <;> ring



/- Exact source owner: SourceShiftTwoPsiUniformVariation.lean; original line 11. -/
theorem source_psi_global_regular_bounds (Ψ : ℝ → ℝ)
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) :
    ∃ S : ℝ, ∃ T : NNReal, 0 ≤ S ∧ (∀ t, |Ψ t| ≤ S) ∧ LipschitzWith T Ψ := by
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  obtain ⟨S,hS⟩ := hc.exists_bound_of_continuous hΨ.continuous
  obtain ⟨T,hT⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hΨ (by simp)
  refine ⟨S,T,(abs_nonneg (Ψ 0)).trans (by simpa only [Real.norm_eq_abs] using hS 0),?_,hT⟩
  intro t
  simpa only [Real.norm_eq_abs] using hS t

/- Exact discrete variation is bounded by S+T*N*R/x, including N=0.
It is the variation appearing in the already checked source Abel theorem. -/



/- Exact source owner: SourceShiftTwoPsiUniformVariation.lean; original line 23. -/
theorem source_psi_discrete_variation_lipschitz
    (Ψ : ℝ → ℝ) (S : ℝ) (T : NNReal) (hS : ∀ t, |Ψ t| ≤ S)
    (hT : LipschitzWith T Ψ) (L : ℝ) (M N R : ℕ) :
    sourcePsiDiscreteVariation Ψ L M N R ≤ S + (T:ℝ)*(N:ℝ)*(R:ℝ)/Real.exp L := by
  have hstep (i : ℕ) :
      ‖(Ψ (((M+(i+1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ) -
        (Ψ (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ)‖ ≤
          (T:ℝ)*(R:ℝ)/Real.exp L := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hh := hT.norm_sub_le
      (((M+(i+1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L)
      (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L)
    have he : (((M+(i+1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) -
        (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) = (R:ℝ)/Real.exp L := by
      push_cast; ring
    simp only [he,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Nat.cast_nonneg R) (Real.exp_pos L).le)] at hh
    simpa only [mul_div_assoc] using hh
  unfold sourcePsiDiscreteVariation
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hsum : (∑ i ∈ Finset.range (N-1),
      ‖(Ψ (((M+(i+1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ) -
        (Ψ (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ)‖) ≤
      (N:ℝ)*((T:ℝ)*(R:ℝ)/Real.exp L) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (N-1), (T:ℝ)*(R:ℝ)/Real.exp L :=
        Finset.sum_le_sum (fun i hi => hstep i)
      _ = ((N-1:ℕ):ℝ)*((T:ℝ)*(R:ℝ)/Real.exp L) := by simp
      _ ≤ (N:ℝ)*((T:ℝ)*(R:ℝ)/Real.exp L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le N 1
  have hh := add_le_add (hS (((M+(N-1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L)) hsum
  calc
    _ ≤ S+(N:ℝ)*((T:ℝ)*(R:ℝ)/Real.exp L) := hh
    _ = _ := by ring

/- Every genuine source box has the same Ψ variation bound S+4T,
uniform in all residual integers in that dyad. -/



/- Exact source owner: SourceShiftTwoPsiUniformVariation.lean; original line 60. -/
theorem source_psi_source_box_variation
    (r₀ : ℕ) (L : ℝ) (J : ℕ) (a : ℕ×ℕ)
    (ha : a ∈ sourceEchiSourceBoxes r₀ L J)
    (Ψ : ℝ → ℝ) (S : ℝ) (T : NNReal)
    (hS : ∀ t, |Ψ t| ≤ S) (hT : LipschitzWith T Ψ)
    (R : ℕ) (hR : R ∈ sourceEchiDyad a.2) :
    sourcePsiDiscreteVariation Ψ L (sourceEchiDyadLower a.1) (2^a.1) R ≤ S+4*(T:ℝ) := by
  have hc := (Finset.mem_filter.mp ha).2.2
  have hdy := (source_echi_dyad_mem a.2 R).mp hR
  have hRu : (R:ℝ) ≤ 2*(2:ℝ)^a.2 := by
    have h : (R:ℝ) < (2:ℝ)^(a.2+1) := by exact_mod_cast hdy.2
    have hh : (R:ℝ) < 2*(2:ℝ)^a.2 := by simpa only [pow_succ,mul_comm] using h
    exact hh.le
  have hprod : (2:ℝ)^a.1*(R:ℝ) ≤ 4*Real.exp L := by
    have hh := mul_le_mul_of_nonneg_left hRu (by positivity : (0:ℝ) ≤ (2:ℝ)^a.1)
    nlinarith [hc.2]
  have hfrac : (T:ℝ)*(2:ℝ)^a.1*(R:ℝ)/Real.exp L ≤ 4*(T:ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos L)).mpr
    have hh := mul_le_mul_of_nonneg_left hprod T.coe_nonneg
    nlinarith
  have hh := source_psi_discrete_variation_lipschitz Ψ S T hS hT L
    (sourceEchiDyadLower a.1) (2^a.1) R
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  exact hh.trans (add_le_add_right hfrac S)

/- Uniform variation obligation discharged from the original regularity
hypotheses, independently of r₀,L,J and all source boxes. -/



/- Exact source owner: SourceShiftTwoPsiUniformVariation.lean; original line 87. -/
theorem source_psi_uniform_source_variation (Ψ : ℝ → ℝ)
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) :
    ∃ S V : ℝ, 0 ≤ S ∧ 0 ≤ V ∧ (∀ t, |Ψ t| ≤ S) ∧
      ∀ (r₀ : ℕ) (L : ℝ) (J : ℕ) (a : ℕ×ℕ),
        a ∈ sourceEchiSourceBoxes r₀ L J → ∀ R ∈ sourceEchiDyad a.2,
          sourcePsiDiscreteVariation Ψ L (sourceEchiDyadLower a.1) (2^a.1) R ≤ V := by
  obtain ⟨S,T,hS0,hS,hT⟩ := source_psi_global_regular_bounds Ψ hΨ hs
  refine ⟨S,S+4*(T:ℝ),hS0,by positivity,hS,?_⟩
  intro r₀ L J a ha R hR
  exact source_psi_source_box_variation r₀ L J a ha Ψ S T hS hT R hR



/- Exact source owner: SourceShiftTwoSWFiniteEchi.lean; original line 12. -/
theorem source_original_SW_finite_Echi_eventually
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (C A θ : ℝ) (hC : 0 < C) (hA : 0 < A) (hθ : 0 < θ) (hθu : θ < 1/2) :
    ∃ B S V : ℝ, 0 ≤ B ∧ 0 ≤ S ∧ 0 ≤ V ∧
      ∀ᶠ L : ℝ in atTop, ∀ (J K T : ℕ), K ≤ T →
        ⌊(Real.exp L)^θ⌋₊ ≤ 2^T → ⌊2*Real.exp L⌋₊ ≤ 2^J-1 →
        ((2^K:ℕ):ℝ) ≤ L^C →
        (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
            (fun d => Odd d ∧ Squarefree d),
          sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
        Real.exp 1*L*∑ a ∈ sourceEchiSourceBoxes r₀ L J,
          (((2^K:ℕ):ℝ)*((2^a.2:ℕ):ℝ)*L^sourceDeletedCoefficientExponent*
            (B*(2:ℝ)^a.1*L^(-A)*V+(θ/sourceOriginalQ0Scale r₀)*S) +
            ∑ s ∈ Finset.Ico K T, sourceEchiLargeBoxBudget Ψ L s a) := by
  obtain ⟨S,V,hS0,hV0,hS,hvar⟩ := source_psi_uniform_source_variation Ψ hΨ hs
  obtain ⟨B,hB,hpref⟩ := source_SW_original_matched_prefixes hSW r₀ hr₀ C A hC hA
  refine ⟨B,S,V,hB,hS0,hV0,?_⟩
  filter_upwards [hpref,source_original_Echi_prefix_terminal_eventually r₀ hr₀,
    eventually_ge_atTop (2:ℝ)] with L hp ht hL
  intro J K T hKT hQ hN hcut
  let H : ℕ×ℕ → ℝ := fun a => B*(2:ℝ)^a.1*L^(-A)
  have hH (a : ℕ×ℕ) : 0 ≤ H a := by dsimp [H]; positivity
  apply ht Ψ hΨ hs θ hθ hθu hL J K T hKT hQ hN H hH V S hV0 hS0 hS
    (hvar r₀ L J)
  intro a ha f hf χ hprim n hn
  have hf1 : f ≠ 1 := by have := (Finset.mem_Ioc.mp hf).1; omega
  have hf0 : f ≠ 0 := by have := (Finset.mem_Ioc.mp hf).1; omega
  letI : NeZero f := ⟨hf0⟩
  have hnon : χ ≠ 1 := by
    intro he
    have hc := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    have hcf : χ.conductor = f := hprim
    exact hf1 (hcf.symm.trans hc)
  have hfc : (f:ℝ) ≤ L^C := by
    have hnat := (Finset.mem_Ioc.mp hf).2
    have hcast : (f:ℝ) ≤ ((2^K:ℕ):ℝ) := by exact_mod_cast hnat
    exact hcast.trans hcut
  exact hp J a ha f χ hprim hnon hfc n hn



/- Exact source owner: SourceShiftTwoSmallScalarBudget.lean; original line 14. -/
theorem source_original_small_scalar_box
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (hL : 0 < L)
    (J K : ℕ) (a : ℕ×ℕ) (ha : a ∈ sourceEchiSourceBoxes r₀ L J)
    (C A θ B S V : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hcut : ((2^K:ℕ):ℝ) ≤ L^C) :
    ((2^K:ℕ):ℝ)*((2^a.2:ℕ):ℝ)*L^sourceDeletedCoefficientExponent*
      (B*(2:ℝ)^a.1*L^(-A)*V+(θ/sourceOriginalQ0Scale r₀)*S) ≤
        sourceEchiSmallScalarBudget r₀ L C A θ B S V := by
  obtain ⟨hpLow,hpHigh,huLow,huHigh,hproduct⟩ :=
    source_original_box_scale_ranges r₀ hr₀ L J a ha
  have hr : (0:ℝ)< r₀ := by exact_mod_cast hr₀
  have hα : 0 < sourceOriginalQ0Scale r₀ := by unfold sourceOriginalQ0Scale; positivity
  have hcoef : 0 ≤ B*L^(-A)*V := by positivity
  have hE : 0 ≤ (θ/sourceOriginalQ0Scale r₀)*S := by positivity
  have hinner :
      B*L^(-A)*V*((2:ℝ)^a.1*(2:ℝ)^a.2) +
        ((θ/sourceOriginalQ0Scale r₀)*S)*(2:ℝ)^a.2 ≤
      B*L^(-A)*V*(2*Real.exp L) +
        ((θ/sourceOriginalQ0Scale r₀)*S)*(4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L)) :=
    add_le_add (mul_le_mul_of_nonneg_left hproduct hcoef)
      (mul_le_mul_of_nonneg_left huHigh hE)
  have hpre : ((2^K:ℕ):ℝ)*L^sourceDeletedCoefficientExponent ≤
      L^C*L^sourceDeletedCoefficientExponent :=
    mul_le_mul_of_nonneg_right hcut (by positivity)
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  unfold sourceEchiSmallScalarBudget
  calc
    _ = ((2^K:ℕ):ℝ)*L^sourceDeletedCoefficientExponent *
        (B*L^(-A)*V*((2:ℝ)^a.1*(2:ℝ)^a.2) +
          ((θ/sourceOriginalQ0Scale r₀)*S)*(2:ℝ)^a.2) := by push_cast; ring
    _ ≤ L^C*L^sourceDeletedCoefficientExponent *
        (B*L^(-A)*V*(2*Real.exp L) +
          ((θ/sourceOriginalQ0Scale r₀)*S)*(4*Real.exp ((1-sourceOriginalQ0Scale r₀)*L))) := by
      exact mul_le_mul hpre hinner (by positivity) (by positivity)
    _ = _ := by ring

/- Quantitative original Echi: all small conductors are now assembled into
one scalar error; only a proved explicit large-sieve sum remains unevaluated.
Foundational primitive SW is still an OPEN hypothesis. -/


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Terminal002 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoSmallScalarBudget.lean; original line 53. -/
theorem source_original_SW_Echi_small_scalar_eventually
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (C A θ : ℝ) (hC : 0 < C) (hA : 0 < A) (hθ : 0 < θ) (hθu : θ < 1/2) :
    ∃ B S V : ℝ, 0 ≤ B ∧ 0 ≤ S ∧ 0 ≤ V ∧
      ∀ᶠ L : ℝ in atTop, ∀ (J K T : ℕ), K ≤ T →
        ⌊(Real.exp L)^θ⌋₊ ≤ 2^T → ⌊2*Real.exp L⌋₊ ≤ 2^J-1 →
        ((2^K:ℕ):ℝ) ≤ L^C →
        (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
            (fun d => Odd d ∧ Squarefree d),
          sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
        Real.exp 1*L*
          (3*(J:ℝ)*sourceEchiSmallScalarBudget r₀ L C A θ B S V +
            ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
              ∑ s ∈ Finset.Ico K T, sourceEchiLargeBoxBudget Ψ L s a) := by
  obtain ⟨B,S,V,hB,hS,hV,hbound⟩ :=
    source_original_SW_finite_Echi_eventually hSW r₀ hr₀ Ψ hΨ hs C A θ hC hA hθ hθu
  refine ⟨B,S,V,hB,hS,hV,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hb hL
  intro J K T hKT hQ hN hcut
  apply (hb J K T hKT hQ hN hcut).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib]
  apply add_le_add_left
  have hscalar : 0 ≤ sourceEchiSmallScalarBudget r₀ L C A θ B S V := by
    have hr : (0:ℝ)< r₀ := by exact_mod_cast hr₀
    have hα : 0 < sourceOriginalQ0Scale r₀ := by unfold sourceOriginalQ0Scale; positivity
    unfold sourceEchiSmallScalarBudget
    positivity
  calc
    _ ≤ ∑ _a ∈ sourceEchiSourceBoxes r₀ L J, sourceEchiSmallScalarBudget r₀ L C A θ B S V :=
      Finset.sum_le_sum (fun a ha =>
        source_original_small_scalar_box r₀ hr₀ L hL J K a ha C A θ B S V hθ.le hB hS hV hcut)
    _ = ((sourceEchiSourceBoxes r₀ L J).card:ℝ)*sourceEchiSmallScalarBudget r₀ L C A θ B S V := by simp
    _ ≤ 3*(J:ℝ)*sourceEchiSmallScalarBudget r₀ L C A θ B S V := by
      apply mul_le_mul_of_nonneg_right _ hscalar
      exact_mod_cast source_original_source_boxes_card r₀ L J



/- Exact source owner: SourceShiftTwoLargeConductorSums.lean; original line 7. -/
theorem source_echi_conductor_geom (K T : ℕ) (hKT : K ≤ T) :
    (∑ s ∈ Finset.Ico K T, (2:ℝ)^s) ≤ (2:ℝ)^T ∧
      (∑ s ∈ Finset.Ico K T, 1/(2:ℝ)^s) ≤ 2/(2:ℝ)^K ∧
      ((Finset.Ico K T).card:ℝ) ≤ T := by
  have hfirst := geom_sum_Ico (K:=ℝ) (x:=(2:ℝ)) (by norm_num) hKT
  have hsecond := geom_sum_Ico (K:=ℝ) (x:=(1/2:ℝ)) (by norm_num) hKT
  simp only [div_pow,one_pow] at hsecond
  norm_num at hfirst hsecond
  refine ⟨?_,?_,?_⟩
  · rw [hfirst]; linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) K]
  · simp only [one_div]
    rw [hsecond]
    have ht : 0 ≤ ((2:ℝ)^T)⁻¹ := by positivity
    norm_num [div_eq_mul_inv]
    linarith
  · simp only [Nat.card_Ico,Nat.cast_sub hKT]
    have hk : (0:ℝ) ≤ K := by positivity
    linarith



/- Exact source owner: SourceShiftTwoLargeBudgetExpansion.lean; original line 7. -/
theorem sqrt_four_sum_le (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a+b+c+d) ≤ Real.sqrt a+Real.sqrt b+Real.sqrt c+Real.sqrt d := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  have h4 := Real.sq_sqrt hd
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg d),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg d),
    mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg d)]

/- Exact quantitative expansion of the proved primitive large-sieve
radicand. It exposes the conductor, balanced-box and reciprocal-conductor
terms needed for genuine Echi summation. -/



/- Exact source owner: SourceShiftTwoLargeBudgetExpansion.lean; original line 26. -/
theorem source_echi_large_radical_expansion (F P U H : ℝ)
    (hF : 0 < F) (hP : 0 ≤ P) (hU : 0 ≤ U) (hH : 0 ≤ H) :
    Real.sqrt (((4*F^2+Real.pi*P)/F)*P) *
      Real.sqrt (((4*F^2+Real.pi*U)/F)*(U*H^2)) ≤
    H*(4*F*Real.sqrt (P*U) +
      2*Real.sqrt Real.pi*Real.sqrt (P*U)*(Real.sqrt P+Real.sqrt U) +
      Real.pi*(P*U)/F) := by
  have hF0 := ne_of_gt hF
  have hPU : 0 ≤ P*U := mul_nonneg hP hU
  let D : ℝ := 16*F^2+4*Real.pi*P+4*Real.pi*U+Real.pi^2*(P*U)/F^2
  have he :
      (((4*F^2+Real.pi*P)/F)*P)*(((4*F^2+Real.pi*U)/F)*(U*H^2)) =
      H^2*((P*U)*D) := by dsimp [D]; field_simp; ring
  have hs1 : Real.sqrt (16*F^2) = 4*F := by
    rw [show 16*F^2 = (4*F)^2 by ring,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs2 : Real.sqrt (4*Real.pi*P) = 2*Real.sqrt Real.pi*Real.sqrt P := by
    rw [show 4*Real.pi*P = (2*Real.sqrt Real.pi*Real.sqrt P)^2 by
      rw [mul_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le,Real.sq_sqrt hP]; ring,
      Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs3 : Real.sqrt (4*Real.pi*U) = 2*Real.sqrt Real.pi*Real.sqrt U := by
    rw [show 4*Real.pi*U = (2*Real.sqrt Real.pi*Real.sqrt U)^2 by
      rw [mul_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le,Real.sq_sqrt hU]; ring,
      Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs4 : Real.sqrt (Real.pi^2*(P*U)/F^2) = Real.pi*Real.sqrt (P*U)/F := by
    rw [show Real.pi^2*(P*U)/F^2 = (Real.pi*Real.sqrt (P*U)/F)^2 by
      rw [div_pow,mul_pow,Real.sq_sqrt hPU],
      Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hb := sqrt_four_sum_le (16*F^2) (4*Real.pi*P) (4*Real.pi*U)
    (Real.pi^2*(P*U)/F^2) (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hs1,hs2,hs3,hs4] at hb
  have hAB : 0 ≤ (((4*F^2+Real.pi*P)/F)*P) := by positivity
  rw [← Real.sqrt_mul hAB,he,Real.sqrt_mul (sq_nonneg H),
    Real.sqrt_sq_eq_abs,abs_of_nonneg hH,Real.sqrt_mul hPU]
  calc
    _ ≤ H*(Real.sqrt (P*U)*
        (4*F+2*Real.sqrt Real.pi*Real.sqrt P+2*Real.sqrt Real.pi*Real.sqrt U+
          Real.pi*Real.sqrt (P*U)/F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)) hH
    _ = _ := by
      have hs := Real.sq_sqrt hPU
      field_simp
      linear_combination H*Real.pi*hs

/- The actual source Ψ large box budget, with original coefficient exponent
and Mellin L1 mass, obeys the explicit expansion for all source dyads. -/



/- Exact source owner: SourceShiftTwoLargeBudgetExpansion.lean; original line 71. -/
theorem source_original_large_box_expanded (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (s : ℕ) (a : ℕ×ℕ) :
    sourceEchiLargeBoxBudget Ψ L s a ≤
      L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ *
        (4*(2:ℝ)^s*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2) +
          2*Real.sqrt Real.pi*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2)*
            (Real.sqrt ((2:ℝ)^a.1)+Real.sqrt ((2:ℝ)^a.2)) +
          Real.pi*((2:ℝ)^a.1*(2:ℝ)^a.2)/(2:ℝ)^s) := by
  have hh := source_echi_large_radical_expansion ((2:ℝ)^s) ((2:ℝ)^a.1) ((2:ℝ)^a.2)
    (L^sourceDeletedCoefficientExponent) (by positivity) (by positivity) (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_right hh (source_log_mellin_mass_nonneg Ψ)
  unfold sourceEchiLargeBoxBudget
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hfour : (2:ℝ)^2 = 4 := by norm_num
  simp only [mul_pow,hfour] at ⊢
  calc
    _ ≤ (L^sourceDeletedCoefficientExponent *
        (4*(2:ℝ)^s*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2) +
          2*Real.sqrt Real.pi*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2)*
            (Real.sqrt ((2:ℝ)^a.1)+Real.sqrt ((2:ℝ)^a.2)) +
          Real.pi*((2:ℝ)^a.1*(2:ℝ)^a.2)/(2:ℝ)^s))*sourceLogMellinMass Ψ := hm
    _ = _ := by ring



/- Exact source owner: SourceShiftTwoLargeScalarGeometry.lean; original line 20. -/
theorem source_original_large_box_scalar (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (J s : ℕ) (a : ℕ×ℕ)
    (ha : a ∈ sourceEchiSourceBoxes r₀ L J) :
    sourceEchiLargeBoxBudget Ψ L s a ≤
      L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ *
        (8*(2:ℝ)^s*Real.exp (L/2) +
          12*Real.sqrt Real.pi*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) +
          2*Real.pi*Real.exp L/(2:ℝ)^s) := by
  obtain ⟨_,hp,_,hu,hpu⟩ := source_original_box_scale_ranges r₀ hr₀ L J a ha
  obtain ⟨hα,hαu⟩ := source_echi_alpha_bounds r₀ hr₀
  have hs (c : ℝ) : (Real.exp (c/2))^2 = Real.exp c := by
    rw [pow_two,← Real.exp_add]; congr 1; ring
  have hroot : Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2) ≤ 2*Real.exp (L/2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,hs]
    nlinarith [Real.exp_pos L]
  have hrootP : Real.sqrt ((2:ℝ)^a.1) ≤
      Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L/2) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by rw [hs]; exact hp⟩
  have hrootU : Real.sqrt ((2:ℝ)^a.2) ≤
      2*Real.exp ((1-sourceOriginalQ0Scale r₀)*L/2) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by rw [mul_pow,hs]; norm_num; exact hu⟩
  have hmidP : Real.exp (L/2) *
      Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L/2) ≤
      Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmidU : Real.exp (L/2) *
      Real.exp ((1-sourceOriginalQ0Scale r₀)*L/2) =
      Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) := by
    rw [← Real.exp_add]; congr 1; ring
  apply (source_original_large_box_expanded Ψ L hL s a).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hL.le _) (source_log_mellin_mass_nonneg Ψ))
  have hfirst : 4*(2:ℝ)^s*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2) ≤
      8*(2:ℝ)^s*Real.exp (L/2) := by nlinarith [mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 4*(2:ℝ)^s)]
  have hlast : Real.pi*((2:ℝ)^a.1*(2:ℝ)^a.2)/(2:ℝ)^s ≤
      2*Real.pi*Real.exp L/(2:ℝ)^s := by
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpu Real.pi_pos.le) (by positivity : (0:ℝ) ≤ (2:ℝ)^s)
    calc
      _ ≤ Real.pi*(2*Real.exp L)/(2:ℝ)^s := hh
      _ = _ := by ring
  have hm1 := mul_le_mul_of_nonneg_left hmidP (by positivity : 0 ≤ 4*Real.sqrt Real.pi)
  have hm2 := mul_le_mul_of_nonneg_left hmidU.le (by positivity : 0 ≤ 8*Real.sqrt Real.pi)
  have hmiddle :
      2*Real.sqrt Real.pi*Real.sqrt ((2:ℝ)^a.1*(2:ℝ)^a.2)*
        (Real.sqrt ((2:ℝ)^a.1)+Real.sqrt ((2:ℝ)^a.2)) ≤
      12*Real.sqrt Real.pi*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) := by
    calc
      _ ≤ 2*Real.sqrt Real.pi*(2*Real.exp (L/2))*
        (Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L/2)+
          2*Real.exp ((1-sourceOriginalQ0Scale r₀)*L/2)) := by gcongr
      _ = 4*Real.sqrt Real.pi*(Real.exp (L/2)*
        Real.exp (((6/5:ℝ)*sourceOriginalQ0Scale r₀)*L/2))+
        8*Real.sqrt Real.pi*(Real.exp (L/2)*
          Real.exp ((1-sourceOriginalQ0Scale r₀)*L/2)) := by ring
      _ ≤ _ := by linarith
  linarith



/- Exact source owner: SourceShiftTwoLargeConductorSums.lean; original line 35. -/
theorem source_original_large_conductor_scalar (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (J K T : ℕ) (hKT : K ≤ T)
    (a : ℕ×ℕ) (ha : a ∈ sourceEchiSourceBoxes r₀ L J) :
    (∑ s ∈ Finset.Ico K T, sourceEchiLargeBoxBudget Ψ L s a) ≤
      sourceEchiLargeScalarBudget r₀ Ψ L K T := by
  obtain ⟨hfirst,hsecond,hcard⟩ := source_echi_conductor_geom K T hKT
  have hH : 0 ≤ L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ :=
    mul_nonneg (Real.rpow_nonneg hL.le _) (source_log_mellin_mass_nonneg Ψ)
  calc
    _ ≤ ∑ s ∈ Finset.Ico K T,
        L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ *
          (8*(2:ℝ)^s*Real.exp (L/2) +
            12*Real.sqrt Real.pi*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) +
            2*Real.pi*Real.exp L/(2:ℝ)^s) :=
      Finset.sum_le_sum (fun s _ => source_original_large_box_scalar r₀ hr₀ Ψ L hL J s a ha)
    _ = L^sourceDeletedCoefficientExponent * sourceLogMellinMass Ψ *
        (8*(∑ s ∈ Finset.Ico K T, (2:ℝ)^s)*Real.exp (L/2) +
          12*Real.sqrt Real.pi*((Finset.Ico K T).card:ℝ)*Real.exp ((1-sourceOriginalQ0Scale r₀/2)*L) +
          2*Real.pi*Real.exp L*(∑ s ∈ Finset.Ico K T, 1/(2:ℝ)^s)) := by
      simp only [mul_add, div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ sourceEchiLargeScalarBudget r₀ Ψ L K T := by
      unfold sourceEchiLargeScalarBudget
      apply mul_le_mul_of_nonneg_left _ hH
      have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0:ℝ) ≤ 8)) (Real.exp_pos (L/2)).le
      have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ 12*Real.sqrt Real.pi)) (Real.exp_pos ((1-sourceOriginalQ0Scale r₀/2)*L)).le
      have hs := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 2*Real.pi*Real.exp L)
      have he : 2*Real.pi*Real.exp L*(2/(2:ℝ)^K) = 4*Real.pi*Real.exp L/(2:ℝ)^K := by ring
      rw [he] at hs
      linarith

/- Finite original Echi with both conductor ranges completely summed.
SW is the sole open analytic cancellation premise. -/



/- Exact source owner: SourceShiftTwoLargeConductorSums.lean; original line 68. -/
theorem source_original_SW_Echi_full_scalar_eventually
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (C A θ : ℝ) (hC : 0 < C) (hA : 0 < A) (hθ : 0 < θ) (hθu : θ < 1/2) :
    ∃ B S V : ℝ, 0 ≤ B ∧ 0 ≤ S ∧ 0 ≤ V ∧
      ∀ᶠ L : ℝ in atTop, ∀ (J K T : ℕ), K ≤ T →
        ⌊(Real.exp L)^θ⌋₊ ≤ 2^T → ⌊2*Real.exp L⌋₊ ≤ 2^J-1 →
        ((2^K:ℕ):ℝ) ≤ L^C →
        (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
            (fun d => Odd d ∧ Squarefree d),
          sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
        3*Real.exp 1*L*(J:ℝ)*
          (sourceEchiSmallScalarBudget r₀ L C A θ B S V +
            sourceEchiLargeScalarBudget r₀ Ψ L K T) := by
  obtain ⟨B,S,V,hB,hS,hV,hbound⟩ :=
    source_original_SW_Echi_small_scalar_eventually hSW r₀ hr₀ Ψ hΨ hs C A θ hC hA hθ hθu
  refine ⟨B,S,V,hB,hS,hV,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with L hb hL
  intro J K T hKT hQ hN hcut
  apply (hb J K T hKT hQ hN hcut).trans
  have hl0 : 0 ≤ sourceEchiLargeScalarBudget r₀ Ψ L K T := by
    unfold sourceEchiLargeScalarBudget
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hL.le _) (source_log_mellin_mass_nonneg Ψ)) (by positivity)
  have hsum : (∑ a ∈ sourceEchiSourceBoxes r₀ L J,
      ∑ s ∈ Finset.Ico K T, sourceEchiLargeBoxBudget Ψ L s a) ≤
      3*(J:ℝ)*sourceEchiLargeScalarBudget r₀ Ψ L K T := by
    calc
      _ ≤ ∑ _a ∈ sourceEchiSourceBoxes r₀ L J, sourceEchiLargeScalarBudget r₀ Ψ L K T :=
        Finset.sum_le_sum (fun a ha => source_original_large_conductor_scalar r₀ hr₀ Ψ L hL J K T hKT a ha)
      _ = ((sourceEchiSourceBoxes r₀ L J).card:ℝ)*sourceEchiLargeScalarBudget r₀ Ψ L K T := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast source_original_source_boxes_card r₀ L J) hl0
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ Real.exp 1*L)
  nlinarith



/- Exact source owner: SourceShiftTwoConditionalEchiSaving.lean; original line 10. -/
theorem source_original_SW_Echi_saving
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (θ D : ℝ) (hθ : 0 < θ) (hθu : θ < 1/2) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ᶠ L : ℝ in atTop,
      (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoCharacterL1 r₀ Ψ L d/(d.totient:ℝ)) ≤
      C_D*Real.exp L*L^(-D) := by
  let k := sourceDeletedCoefficientExponent+D+2
  let C := k+1
  let A := C+sourceDeletedCoefficientExponent+D+2
  have hk : 0 < k := by dsimp [k]; linarith [source_echi_coefficient_exponent_pos]
  have hC : 0 < C := by dsimp [C]; linarith
  have hA : 0 < A := by dsimp [A]; linarith [source_echi_coefficient_exponent_pos]
  obtain ⟨B,S,V,hB,hS,hV,hfinite⟩ :=
    source_original_SW_Echi_full_scalar_eventually hSW r₀ hr₀ Ψ hΨ hs C A θ hC hA hθ hθu
  let c := sourceEchiTerminalConstant r₀ Ψ θ B S V
  have hc : 0 ≤ c := by
    obtain ⟨hα,_⟩ := source_echi_alpha_bounds r₀ hr₀
    have hm := source_log_mellin_mass_nonneg Ψ
    have ht : 0 ≤ sourceEchiTConstant θ := by
      unfold sourceEchiTConstant
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    dsimp [c,sourceEchiTerminalConstant]
    positivity
  have hJc : 0 ≤ sourceEchiJConstant := by
    unfold sourceEchiJConstant
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨3*Real.exp 1*sourceEchiJConstant*c,by positivity,?_⟩
  have hbud := source_echi_terminal_budget_eventually r₀ hr₀ Ψ θ D B S V hθ hθu hD hB hS hV
  filter_upwards [hfinite,hbud,source_echi_terminal_scales r₀ k θ hk hθ,
    eventually_ge_atTop (2:ℝ)] with L hf hb hsc hL
  have hL0 : 0 < L := by linarith
  obtain ⟨J,K,T,hKT,hQ,hN,hK,hKu,hT,hJ,hTc⟩ := hsc
  have hcut : ((2^K:ℕ):ℝ) ≤ L^C := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,C] using hKu
  have hmain := hf J K T hKT hQ hN hcut
  have hsmalllarge : sourceEchiSmallScalarBudget r₀ L C A θ B S V+
      sourceEchiLargeScalarBudget r₀ Ψ L K T ≤ c*Real.exp L*L^(-D-2) := by
    exact hb K T hK hT hTc
  have hj := mul_le_mul_of_nonneg_left hJ
    (by positivity : 0 ≤ 3*Real.exp 1*L*(c*Real.exp L*L^(-D-2)))
  have he : L*L*L^(-D-2) = L^(-D) := by
    calc
      _ = L^(2:ℝ)*L^(-D-2) := by rw [show L^(2:ℝ)=L^2 by simpa using Real.rpow_natCast L 2]; ring
      _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring
  calc
    _ ≤ 3*Real.exp 1*L*(J:ℝ)*
        (sourceEchiSmallScalarBudget r₀ L C A θ B S V+sourceEchiLargeScalarBudget r₀ Ψ L K T) := hmain
    _ ≤ 3*Real.exp 1*L*(J:ℝ)*(c*Real.exp L*L^(-D-2)) :=
      mul_le_mul_of_nonneg_left hsmalllarge (by positivity)
    _ ≤ 3*Real.exp 1*L*(sourceEchiJConstant*L)*(c*Real.exp L*L^(-D-2)) := by nlinarith
    _ = (3*Real.exp 1*sourceEchiJConstant*c)*Real.exp L*(L*L*L^(-D-2)) := by ring
    _ = _ := by rw [he]



/- Exact source owner: SourceShiftTwoConditionalCongruence.lean; original line 9. -/
theorem source_original_SW_Echi_saving_x
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (θ D : ℝ) (hθ : 0 < θ) (hθu : θ < 1/2) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.range (⌊x^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoCharacterL1 r₀ Ψ (Real.log x) d/(d.totient:ℝ)) ≤
      C_D*x*(Real.log x)^(-D) := by
  obtain ⟨C,hC,hbound⟩ := source_original_SW_Echi_saving hSW r₀ hr₀ Ψ hΨ hs θ D hθ hθu hD
  refine ⟨C,hC,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbound,eventually_gt_atTop (0:ℝ)] with x hx hx0
  simpa only [Real.exp_log hx0] using hx

/- Original residue u=-2 congruence with the already proved full principal
nonunit correction. This remains conditional on foundational SW. -/



/- Exact source owner: SourceSWUnconditionalEchi.lean; original line 9. -/
theorem source_original_SW_Echi_saving_x_unconditional
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (θ D : ℝ) (hθ : 0 < θ) (hθu : θ < 1/2) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.range (⌊x^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoCharacterL1 r₀ Ψ (Real.log x) d/(d.totient:ℝ)) ≤
      C_D*x*(Real.log x)^(-D) :=
  source_original_SW_Echi_saving_x sourcePrimeSiegelWalfisz_unconditional
    r₀ hr₀ Ψ hΨ hs θ D hθ hθu hD

/- The actual u = -2 congruence contract, now unconditional. -/



/- Exact source owner: SourceShiftTwoCongruenceSieve.lean; original line 9. -/
noncomputable def sourceShiftTwoDivisorMass (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2 * Real.exp L⌋₊+1),
    if d ∣ u+2 then sourceOriginalMovingWeight r₀ Ψ L u else 0



/- Exact source owner: SourceShiftTwoCongruenceSieve.lean; original line 13. -/
noncomputable def sourceShiftTwoRemainder (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  sourceShiftTwoDivisorMass r₀ Ψ L d -
    sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ / (d.totient : ℝ)

/- UNPROVED analytic input, with relative errors summed over the actual
odd squarefree divisors. This is a predicate, not an asserted theorem. -/



/- Exact source owner: SourceShiftTwoCongruenceSieve.lean; original line 21. -/
def SourceShiftTwoCongruenceInput (r₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ θ D : ℝ, 0 < θ → θ < 1/2 → 0 < D →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in Filter.atTop,
      (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d), |sourceShiftTwoRemainder r₀ Ψ L d|) ≤
      C * (Real.exp L * L^(-D) +
        sourceOriginalXA r₀
          (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
          (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ * L^(-18:ℝ))

/- Distinct prime divisors impose exactly a squarefree product divisor. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 77. -/
theorem source_original_ordinary_nonneg
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ) :
    0 ≤ sourceOriginalOrdinaryCoefficient r Q v := by
  unfold sourceOriginalOrdinaryCoefficient
  split_ifs <;> positivity

/- The literal marked weight is nonnegative; omega is distinct-counted. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 94. -/
theorem source_original_A0_nonneg
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (u : ℕ) : 0 ≤ sourceOriginalA0 r Q P u := by
  unfold sourceOriginalA0
  exact mul_nonneg (source_original_W1_nonneg P u)
    (source_original_ordinary_nonneg r Q _)

/- No parity reinterpretation: the actual Ω-exponent projection
takes precisely the values 0 and 1. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 119. -/
theorem source_original_parity_pointwise
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (u : ℕ) :
    0 ≤ sourceOriginalA r Q P u ∧
      sourceOriginalA r Q P u ≤ sourceOriginalA0 r Q P u := by
  rcases source_original_parity_projection_zero_or_one
    (Finset.univ.biUnion P) u with h | h
  · simp [sourceOriginalA, h, source_original_A0_nonneg r Q P u]
  · simp [sourceOriginalA, h, source_original_A0_nonneg r Q P u]

/- The exact original P-supported companion factor of u_*. -/



/- Exact source owner: SourceShiftTwoHarmonicNormalization.lean; original line 81. -/
theorem source_original_XA_nonneg
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) (hPsi : ∀ t, 0 ≤ Ψ t) :
    0 ≤ sourceOriginalXA r Q P x Ψ := by
  unfold sourceOriginalXA
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (source_original_parity_pointwise r Q P u).1
    (hPsi _)



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 34. -/
noncomputable def sourceShiftTwoNonunitMass
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
    if ¬IsUnit (u : ZMod d) then sourceOriginalMovingWeight r₀ Ψ L u else 0

/- The genuine source remainder is bounded by the actual character ℓ¹
majorant plus the principal correction. No distribution estimate is assumed. -/



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 16. -/
theorem source_shift_two_divisor_class (d u : ℕ) :
    d ∣ u+2 ↔ (u : ZMod d) = -2 := by
  rw [← ZMod.natCast_eq_zero_iff (u+2) d]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  exact add_eq_zero_iff_eq_neg

/- Actual nonprincipal character mass. The d=0 branch only makes the
definition total; no theorem below uses that branch. -/



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 9. -/
theorem source_shift_two_neg_two_unit (d : ℕ) (hd : Odd d) :
    IsUnit (-2 : ZMod d) := by
  have htwo : IsUnit (2 : ZMod d) :=
    (ZMod.isUnit_iff_coprime 2 d).mpr ((Nat.coprime_two_right.mpr hd).symm)
  simpa using htwo.neg

/- Exact natural-divisibility correspondence; the endpoint is u+2. -/



/- Exact source owner: SourceShiftTwoCharacterTransfer.lean; original line 13. -/
theorem source_character_unit_norm {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) {a : ZMod d} (ha : IsUnit a) :
    ‖χ a‖ = 1 := by
  have hm : star (χ a) * χ a = 1 := by
    rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply ha]
  have hn := congrArg norm hm
  simp only [norm_mul, norm_star, norm_one] at hn
  have hnon : 0 ≤ ‖χ a‖ := norm_nonneg _
  nlinarith

/- Exact weighted unit-class character identity, before separating the
principal correction. It holds also at d=1. -/



/- Exact source owner: SourceShiftTwoCharacterTransfer.lean; original line 25. -/
theorem source_weighted_unit_class_characters {d : ℕ} [NeZero d]
    (S : Finset ℕ) (w : ℕ → ℂ) {a : ZMod d} (ha : IsUnit a) :
    (d.totient:ℂ) * (∑ u ∈ S, if (u:ZMod d) = a then w u else 0) =
      ∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * ∑ u ∈ S, w u * χ (u:ZMod d) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hh := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (u:ZMod d)
  symm
  calc
    _ = w u * (∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * χ (u:ZMod d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = w u * (if a = (u:ZMod d) then (d.totient:ℂ) else 0) := by rw [hh]
    _ = _ := by
      by_cases h : (u:ZMod d) = a
      · simp [h, mul_comm]
      · simp [h, Ne.symm h]

/- Exact nonprincipal expansion with the principal nonunit correction.
No rough-support assertion is needed to prove this finite identity. -/



/- Exact source owner: SourceShiftTwoCharacterTransfer.lean; original line 50. -/
theorem source_unit_class_remainder_identity {d : ℕ} [NeZero d]
    (S : Finset ℕ) (w : ℕ → ℂ) {a : ZMod d} (ha : IsUnit a) :
    (d.totient:ℂ) * (∑ u ∈ S, if (u:ZMod d) = a then w u else 0) -
        (∑ u ∈ S, w u) =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        χ a⁻¹ * ∑ u ∈ S, w u * χ (u:ZMod d)) -
      (∑ u ∈ S, if ¬IsUnit (u:ZMod d) then w u else 0) := by
  classical
  have hainv : IsUnit a⁻¹ := by
    apply isUnit_iff_exists.mpr
    have he := (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl
    exact ⟨a, he, by simpa [mul_comm] using he⟩
  have hall := source_weighted_unit_class_characters S w ha
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ a⁻¹ * ∑ u ∈ S, w u * χ (u:ZMod d)) (Finset.mem_univ 1)
  have hprincipal : (1 : DirichletCharacter ℂ d) a⁻¹ *
      (∑ u ∈ S, w u * (1 : DirichletCharacter ℂ d) (u:ZMod d)) =
      (∑ u ∈ S, w u) - (∑ u ∈ S, if ¬IsUnit (u:ZMod d) then w u else 0) := by
    rw [MulChar.one_apply hainv, one_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : IsUnit (u:ZMod d)
    · rw [MulChar.one_apply h]
      simp [h]
    · rw [MulChar.map_nonunit _ h]
      simp [h]
  rw [← hsplit, hprincipal] at hall
  linear_combination hall

/- All unit residue classes have the SAME nonprincipal ℓ¹ majorant.
Thus replacing -2⁻¹ by -2 incurs no new analytic character estimate. -/



/- Exact source owner: SourceShiftTwoCharacterTransfer.lean; original line 81. -/
theorem source_unit_class_remainder_bound {d : ℕ} [NeZero d]
    (S : Finset ℕ) (w : ℕ → ℝ) {a : ZMod d} (ha : IsUnit a)
    (hw : ∀ u ∈ S, 0 ≤ w u) :
    |(d.totient:ℝ) * (∑ u ∈ S, if (u:ZMod d) = a then w u else 0) -
        (∑ u ∈ S, w u)| ≤
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖∑ u ∈ S, (w u:ℂ) * χ (u:ZMod d)‖) +
      (∑ u ∈ S, if ¬IsUnit (u:ZMod d) then w u else 0) := by
  classical
  have hainv : IsUnit a⁻¹ := by
    apply isUnit_iff_exists.mpr
    have he := (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl
    exact ⟨a, he, by simpa [mul_comm] using he⟩
  have hh := source_unit_class_remainder_identity S (fun u => (w u:ℂ)) ha
  have hb : ‖∑ u ∈ S, if ¬IsUnit (u:ZMod d) then (w u:ℂ) else 0‖ =
      ∑ u ∈ S, if ¬IsUnit (u:ZMod d) then w u else 0 := by
    have he : (∑ u ∈ S, if ¬IsUnit (u:ZMod d) then (w u:ℂ) else 0) =
        ((∑ u ∈ S, if ¬IsUnit (u:ZMod d) then w u else 0):ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    apply Finset.sum_nonneg
    intro u hu
    split_ifs <;> first | exact hw u hu | positivity
  have hn := norm_sub_le
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
      χ a⁻¹ * ∑ u ∈ S, (w u:ℂ) * χ (u:ZMod d))
    (∑ u ∈ S, if ¬IsUnit (u:ZMod d) then (w u:ℂ) else 0)
  have hc : ‖∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
      χ a⁻¹ * ∑ u ∈ S, (w u:ℂ) * χ (u:ZMod d)‖ ≤
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖∑ u ∈ S, (w u:ℂ) * χ (u:ZMod d)‖ := by
    calc
      _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖χ a⁻¹ * ∑ u ∈ S, (w u:ℂ) * χ (u:ZMod d)‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [norm_mul, source_character_unit_norm χ hainv, one_mul]
  rw [← hh, hb] at hn
  have he : ((d.totient:ℂ) * (∑ u ∈ S, if (u:ZMod d) = a then (w u:ℂ) else 0) -
      (∑ u ∈ S, (w u:ℂ))) =
      (((d.totient:ℝ) * (∑ u ∈ S, if (u:ZMod d) = a then w u else 0) -
      (∑ u ∈ S, w u):ℝ):ℂ)  := by
    push_cast
    congr 2
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> simp
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hn
  exact hn.trans (add_le_add hc (le_refl _))


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Terminal003 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 41. -/
theorem source_shift_two_genuine_remainder_bound
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (d : ℕ)
    (hd : Odd d) (hΨ : ∀ t, 0 ≤ Ψ t) :
    |sourceShiftTwoRemainder r₀ Ψ L d| ≤
      (sourceShiftTwoCharacterL1 r₀ Ψ L d +
        sourceShiftTwoNonunitMass r₀ Ψ L d) / (d.totient : ℝ) := by
  classical
  have hd0 : d ≠ 0 := by
    intro hzero
    subst d
    simpa using hd
  letI : NeZero d := ⟨hd0⟩
  have hφ : 0 < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
  have hw (u : ℕ) :
      0 ≤ sourceOriginalMovingWeight r₀ Ψ L u := by
    unfold sourceOriginalMovingWeight
    exact mul_nonneg (source_original_parity_pointwise _ _ _ _).1 (hΨ _)
  have hbound := source_unit_class_remainder_bound
    (Finset.range (⌊2*Real.exp L⌋₊+1))
    (sourceOriginalMovingWeight r₀ Ψ L) (source_shift_two_neg_two_unit d hd)
    (fun u _ => hw u)
  have hmass :
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if (u : ZMod d) = -2 then sourceOriginalMovingWeight r₀ Ψ L u else 0) =
        sourceShiftTwoDivisorMass r₀ Ψ L d := by
    unfold sourceShiftTwoDivisorMass
    apply Finset.sum_congr rfl
    intro u hu
    exact if_congr (source_shift_two_divisor_class d u).symm rfl rfl
  have htotal :
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        sourceOriginalMovingWeight r₀ Ψ L u) =
      sourceOriginalXA r₀
        (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := rfl
  rw [hmass, htotal] at hbound
  have hbound' : |(d.totient : ℝ) * sourceShiftTwoDivisorMass r₀ Ψ L d -
      sourceOriginalXA r₀
        (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ| ≤
      sourceShiftTwoCharacterL1 r₀ Ψ L d + sourceShiftTwoNonunitMass r₀ Ψ L d := by
    have hnonunit : sourceShiftTwoNonunitMass r₀ Ψ L d =
        ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          if ¬IsUnit (u : ZMod d) then sourceOriginalMovingWeight r₀ Ψ L u else 0 := by
      unfold sourceShiftTwoNonunitMass
      apply Finset.sum_congr rfl
      intro u hu
      by_cases h : IsUnit (u : ZMod d) <;> simp [h]
    rw [hnonunit]
    have hdec :
        (fun a b : DirichletCharacter ℂ d => FunLike.toDecidableEq a b) =
        (fun a b : DirichletCharacter ℂ d => Classical.propDecidable (a = b)) :=
      Subsingleton.elim _ _
    have herase := congrArg
      (fun dec : DecidableEq (DirichletCharacter ℂ d) =>
        @Finset.erase (DirichletCharacter ℂ d) dec Finset.univ 1) hdec
    rw [herase] at hbound
    simpa only [sourceShiftTwoCharacterL1, dif_neg hd0] using hbound
  apply (le_div_iff₀ hφ).mpr
  have he :
        (d.totient : ℝ) * sourceShiftTwoRemainder r₀ Ψ L d =
        (d.totient : ℝ) * sourceShiftTwoDivisorMass r₀ Ψ L d -
          sourceOriginalXA r₀
            (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
            (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
      unfold sourceShiftTwoRemainder
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hφ)]
  rw [← he, abs_mul, abs_of_pos hφ] at hbound'
  simpa [mul_comm] using hbound'

/- Sum over any actual collection of odd moduli. In particular this includes
the original odd squarefree range d ≤ x^θ, without a hidden factor Q. -/



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 106. -/
theorem source_shift_two_genuine_remainder_sum
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (M : Finset ℕ)
    (hM : ∀ d ∈ M, Odd d) (hΨ : ∀ t, 0 ≤ Ψ t) :
    (∑ d ∈ M, |sourceShiftTwoRemainder r₀ Ψ L d|) ≤
      (∑ d ∈ M, sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ)) +
      (∑ d ∈ M, sourceShiftTwoNonunitMass r₀ Ψ L d / (d.totient : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  simpa only [add_div] using
    source_shift_two_genuine_remainder_bound r₀ Ψ L d (hM d hd) hΨ

/- Exact specialization to the modulus range in SourceShiftTwoCongruenceInput. -/



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 119. -/
theorem source_shift_two_actual_range_remainder_sum
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L θ : ℝ) (hΨ : ∀ t, 0 ≤ Ψ t) :
    let M := (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
      (fun d => Odd d ∧ Squarefree d)
    (∑ d ∈ M, |sourceShiftTwoRemainder r₀ Ψ L d|) ≤
      (∑ d ∈ M, sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ)) +
      (∑ d ∈ M, sourceShiftTwoNonunitMass r₀ Ψ L d / (d.totient : ℝ)) := by
  dsimp only
  apply source_shift_two_genuine_remainder_sum r₀ Ψ L _ _ hΨ
  intro d hd
  exact (Finset.mem_filter.mp hd).2.1



/- Exact source owner: SourceShiftTwoNonunitHarmonic.lean; original line 7. -/
theorem shift_two_squarefree_multiple_totient_harmonic
    (M : Finset ℕ) (N p : ℕ) (hp : p.Prime)
    (hM : ∀ d ∈ M, Squarefree d ∧ d ≤ N) :
    (∑ d ∈ M.filter (fun d => p ∣ d), (d.totient : ℝ)⁻¹) ≤
      ((p : ℝ)-1)⁻¹ * sourceSquarefreeTotientSum N := by
  let T := M.filter (fun d => p ∣ d)
  let U := (Finset.Icc 1 N).filter Squarefree
  let f : ℕ → ℕ := fun d => d/p
  have hpd (d : ℕ) (hd : d ∈ T) : p ∣ d := (Finset.mem_filter.mp hd).2
  have he (d : ℕ) (hd : d ∈ T) : p * f d = d := by
    dsimp [f]
    simpa only [mul_comm] using Nat.div_mul_cancel (hpd d hd)
  have hsf (d : ℕ) (hd : d ∈ T) : Squarefree (f d) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (hpd d hd))
      (hM d (Finset.mem_filter.mp hd).1).1
  have hf : Set.InjOn f (↑T : Set ℕ) := by
    intro d hd e he' h
    exact (Nat.div_left_inj (hpd d hd) (hpd e he')).mp h
  have hs : T.image f ⊆ U := by
    intro e he'
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he'
    have hpos : 1 ≤ f d := Nat.one_le_iff_ne_zero.mpr (hsf d hd).ne_zero
    have hle : f d ≤ N := (Nat.div_le_self d p).trans (hM d (Finset.mem_filter.mp hd).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos,hle⟩,hsf d hd⟩
  have ht (d : ℕ) (hd : d ∈ T) : (d.totient : ℝ)⁻¹ =
      ((p : ℝ)-1)⁻¹ * ((f d).totient : ℝ)⁻¹ := by
    have hsfprod : Squarefree (p*f d) := by
      rw [he d hd]
      exact (hM d (Finset.mem_filter.mp hd).1).1
    have hc := Nat.coprime_of_squarefree_mul hsfprod
    conv_lhs => rw [← he d hd]
    rw [Nat.totient_mul hc, Nat.cast_mul, mul_inv_rev,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have ha : 0 ≤ ((p : ℝ)-1)⁻¹ := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    positivity
  calc
    _ = ((p : ℝ)-1)⁻¹ * ∑ e ∈ T.image f, (e.totient : ℝ)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_image hf]
      exact Finset.sum_congr rfl ht
    _ ≤ ((p : ℝ)-1)⁻¹ * ∑ e ∈ U, (e.totient : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ ha
      exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun e he hn => by positivity)
    _ = _ := by simp only [sourceSquarefreeTotientSum, U, Finset.sum_filter]

/- Full-range nonunit reciprocal moment using the elementary harmonic cap. -/



/- Exact source owner: SourceShiftTwoNonunitHarmonic.lean; original line 54. -/
theorem shift_two_nonunit_reciprocal_harmonic
    (M : Finset ℕ) (N u : ℕ) (hu : u ≠ 0)
    (hM : ∀ d ∈ M, Squarefree d ∧ d ≤ N) :
    (∑ d ∈ M, if ¬u.Coprime d then (d.totient : ℝ)⁻¹ else 0) ≤
      (∑ p ∈ u.primeFactors, ((p : ℝ)-1)⁻¹) * sourceSquarefreeTotientSum N := by
  have hpoint (d : ℕ) (hd : d ∈ M) :
      (if ¬u.Coprime d then (d.totient : ℝ)⁻¹ else 0) ≤
        ∑ p ∈ u.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
    have hn (p : ℕ) : 0 ≤ (if p ∣ d then (d.totient : ℝ)⁻¹ else 0) := by positivity
    by_cases hc : u.Coprime d
    · simp only [not_not.mpr hc, if_false]
      exact Finset.sum_nonneg (fun p hp => hn p)
    · rw [if_pos hc]
      obtain ⟨p, hp, hpu, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hpm := Nat.mem_primeFactors.mpr ⟨hp,hpu,hu⟩
      have hh := Finset.single_le_sum (fun q hq => hn q) hpm
      simpa only [if_pos hpd] using hh
  calc
    _ ≤ ∑ d ∈ M, ∑ p ∈ u.primeFactors,
        if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := Finset.sum_le_sum hpoint
    _ = ∑ p ∈ u.primeFactors, ∑ d ∈ M.filter (fun d => p ∣ d),
        (d.totient : ℝ)⁻¹ := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
    _ ≤ ∑ p ∈ u.primeFactors, ((p : ℝ)-1)⁻¹ * sourceSquarefreeTotientSum N := by
      apply Finset.sum_le_sum
      intro p hp
      exact shift_two_squarefree_multiple_totient_harmonic M N p
        (Nat.mem_primeFactors.mp hp).1 hM
    _ = _ := by rw [Finset.sum_mul]



/- Exact source owner: SourceShiftTwoNonunitEuler.lean; original line 106. -/
theorem shift_two_prime_reciprocal_rough_bound
    (u : ℕ) (L : ℝ) (hu : u ≠ 0) (hL : 2 ≤ L)
    (hupper : (u : ℝ) ≤ 2*Real.exp L)
    (hrough : ∀ p ∈ u.primeFactors, L^20 ≤ (p : ℝ)) :
    (∑ p ∈ u.primeFactors, ((p : ℝ)-1)⁻¹) ≤
      (4 / Real.log 2) * L / L^20 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < L := by linarith
  have hpow : (2 : ℕ)^u.primeFactors.card ≤ u := by
    calc
      _ = ∏ _p ∈ u.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ u.primeFactors, p := by
        exact Finset.prod_le_prod₀ (fun p hp => Nat.zero_le _)
          (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
      _ ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu) (Nat.prod_primeFactors_dvd u)
  have hreal : (2 : ℝ)^u.primeFactors.card ≤ (u : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ)^u.primeFactors.card)
    (hreal.trans hupper)
  rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlog2le : Real.log 2 ≤ L := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by linarith)
  have hcard : (u.primeFactors.card : ℝ) ≤ 2*L / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    linarith
  have hp20 : 2 ≤ L^20 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 20
    norm_num at this
    linarith
  have hone (p : ℕ) (hp : p ∈ u.primeFactors) :
      ((p : ℝ)-1)⁻¹ ≤ 2/L^20 := by
    have hpr := hrough p hp
    have hpos : 0 < (p : ℝ)-1 := by linarith
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hpos (by positivity : 0 < L^20)).mpr
    nlinarith
  calc
    _ ≤ ∑ _p ∈ u.primeFactors, 2/L^20 := Finset.sum_le_sum hone
    _ = (u.primeFactors.card : ℝ)*(2/L^20) := by simp
    _ ≤ (2*L/Real.log 2)*(2/L^20) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring



/- Exact source owner: SourceShiftTwoRoughSupport.lean; original line 49. -/
theorem source_shift_two_actual_band_roughness
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      (∀ j p, p ∈ sourceOriginalQActualBands r₀
        (sourceOriginalLiteralDepth r₀ L) L j → L^20 ≤ (p : ℝ)) ∧
      (∀ g p, p ∈ sourceOriginalPAllActualBands r₀ L g → L^20 ≤ (p : ℝ)) := by
  have hSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1/10)).bound (by norm_num : (0 : ℝ) < 1/20)
  filter_upwards [source_original_literal_depth_properties_eventually r₀ hr₀,
    hSmall, eventually_gt_atTop (1 : ℝ)] with L hd hSmallL hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL.le
  have hLp : 0 ≤ L^(1/10 : ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg hLp] at hSmallL
  have hPlog : 20*Real.log L ≤ L^(1/10 : ℝ) := by linarith
  have he : Real.exp (20*Real.log L) = L^20 := by
    rw [← Real.rpow_natCast L 20, Real.rpow_def_of_pos hL0]
    congr 1
    ring
  constructor
  · intro j p hp
    have hscale := source_original_admissible_all_scales r₀
      (sourceOriginalLiteralDepth r₀ L) j.val L hr₀ hL0.le hd.1
      (by have := j.isLt; omega)
    have hrange := (source_original_Q_actual_prime_range r₀
      (sourceOriginalLiteralDepth r₀ L) L hr₀ j p hp).1
    rw [← source_original_Q_actual_scale_eq_P_scale r₀ j.val L hr₀] at hrange
    rw [← he]
    exact (Real.exp_le_exp.mpr hscale).trans hrange
  · intro g p hp
    have hscale := source_original_P_all_actual_band_lower r₀ L hL.le g
    have hrange := (source_original_P_closed_range
      ((3/2 : ℝ)*sourceOriginalPGroupScale r₀ L g.val) p hp).1
    rw [← he]
    exact (Real.exp_le_exp.mpr (hPlog.trans hscale)).trans hrange

/- The rough-support assertion used in the source principal correction is
proved for the literal moving weight, not imposed as a new hypothesis. -/



/- Exact source owner: SourceShiftTwoRoughSupport.lean; original line 11. -/
theorem source_shift_two_weight_prime_alphabet
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (u p : ℕ)
    (hQ : ∀ b q, q ∈ Q b → q.Prime)
    (hA : sourceOriginalA r Q P u ≠ 0) (hp : p.Prime) (hpu : p ∣ u) :
    p ∈ Finset.univ.biUnion P ∨ ∃ b, p ∈ Q b := by
  classical
  have hu : u ≠ 0 := by
    intro hz
    apply hA
    simp [hz, sourceOriginalA, sourceOriginalPParityExponent]
  have hCoeff : sourceOriginalOrdinaryCoefficient r Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) ≠ 0 := by
    intro hz
    apply hA
    simp [sourceOriginalA, sourceOriginalA0, hz]
  have ht : ∃ f : (b : B) → Fin r → {q // q ∈ Q b},
      (∏ b : B, ∏ i : Fin r, (f b i).val) =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
    by_contra hn
    exact hCoeff (by simp [sourceOriginalOrdinaryCoefficient, hn])
  by_cases hP : p ∈ Finset.univ.biUnion P
  · exact Or.inl hP
  · right
    obtain ⟨f, hf⟩ := ht
    have hOrd := source_ordinary_part_dvd_of_not_mem
      (Finset.univ.biUnion P) u p hu hp hpu hP
    rw [← hf] at hOrd
    obtain ⟨b, _, hb⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun b : B => ∏ i : Fin r, (f b i).val)).mp hOrd
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun i : Fin r => (f b i).val)).mp hb
    have he : p = (f b i).val :=
      (Nat.prime_dvd_prime_iff_eq hp (hQ b _ (f b i).property)).mp hi
    exact ⟨b, he ▸ (f b i).property⟩

/- The original moving-depth prime bands are genuinely L^20-rough.
This is derived from literal depth admissibility and all-group geometry. -/



/- Exact source owner: SourceShiftTwoRoughSupport.lean; original line 88. -/
theorem source_shift_two_actual_weight_roughness
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ u p,
      sourceOriginalMovingWeight r₀ Ψ L u ≠ 0 →
      p.Prime → p ∣ u → L^20 ≤ (p : ℝ) := by
  filter_upwards [source_shift_two_actual_band_roughness r₀ hr₀] with L hb u p hw hp hpu
  have hA : sourceOriginalA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) u ≠ 0 := by
    intro hz
    apply hw
    simp [sourceOriginalMovingWeight, hz]
  rcases source_shift_two_weight_prime_alphabet r₀ _ _ u p
    (source_original_Q_actual_prime r₀ (sourceOriginalLiteralDepth r₀ L) L)
    hA hp hpu with hP | ⟨j, hQ⟩
  · obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hP
    exact hb.2 g p hpg
  · exact hb.1 j p hQ

/- At prime 2 the shifted source divisor mass is zero. There is no
1/phi(2) sieve density for this odd-supported source. -/



/- Exact source owner: SourceShiftTwoNonunitHarmonic.lean; original line 83. -/
lemma source_squarefree_totient_sum_nonneg (N : ℕ) :
    0 ≤ sourceSquarefreeTotientSum N := by
  unfold sourceSquarefreeTotientSum
  apply Finset.sum_nonneg
  intro d hd
  split_ifs <;> positivity



/- Exact source owner: SourceShiftTwoNonunitSaving.lean; original line 9. -/
theorem source_shift_two_nonunit_full_range_harmonic
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (hΨ : ∀ t, 0 ≤ Ψ t)
    (θ : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      let N := ⌊(Real.exp L)^θ⌋₊
      let M := (Finset.range (N+1)).filter (fun d => Odd d ∧ Squarefree d)
      (∑ d ∈ M, sourceShiftTwoNonunitMass r₀ Ψ L d / (d.totient : ℝ)) ≤
        ((4 / Real.log 2) * L / L^20 * sourceSquarefreeTotientSum N) *
          sourceOriginalXA r₀
            (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
            (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  filter_upwards [source_shift_two_actual_weight_roughness r₀ hr₀ Ψ,
    eventually_ge_atTop (2 : ℝ)] with L hrough hL
  dsimp only
  let N := ⌊(Real.exp L)^θ⌋₊
  let M := (Finset.range (N+1)).filter (fun d => Odd d ∧ Squarefree d)
  let S := Finset.range (⌊2*Real.exp L⌋₊+1)
  let w := sourceOriginalMovingWeight r₀ Ψ L
  let K := (4 / Real.log 2) * L / L^20
  have hM : ∀ d ∈ M, Squarefree d ∧ d ≤ N := by
    intro d hd
    have hh := Finset.mem_filter.mp hd
    exact ⟨hh.2.2, by have := Finset.mem_range.mp hh.1; omega⟩
  have hw : ∀ u, 0 ≤ w u := fun u =>
    mul_nonneg (source_original_parity_pointwise _ _ _ _).1 (hΨ _)
  have hE : 0 ≤ sourceSquarefreeTotientSum N := source_squarefree_totient_sum_nonneg N
  have hpoint (u : ℕ) (hu : u ∈ S) :
      w u * (∑ d ∈ M, if ¬u.Coprime d then (d.totient : ℝ)⁻¹ else 0) ≤
        w u * (K * sourceSquarefreeTotientSum N) := by
    by_cases hw0 : w u = 0
    · simp [hw0]
    · have hu0 : u ≠ 0 := by
        intro hz
        have hb := hrough u 2 hw0 Nat.prime_two (by simp [hz])
        have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 20
        norm_num at hb hl
        linarith
      have hupper : (u : ℝ) ≤ 2*Real.exp L := by
        have hle : u ≤ ⌊2*Real.exp L⌋₊ := by
          have := Finset.mem_range.mp hu
          omega
        exact (Nat.cast_le.mpr hle).trans (Nat.floor_le (by positivity))
      have hsum := shift_two_nonunit_reciprocal_harmonic M N u hu0 hM
      have hsmall := shift_two_prime_reciprocal_rough_bound u L hu0 hL hupper
        (fun p hp => hrough u p hw0 (Nat.mem_primeFactors.mp hp).1
          (Nat.mem_primeFactors.mp hp).2.1)
      exact mul_le_mul_of_nonneg_left
        (hsum.trans (mul_le_mul_of_nonneg_right hsmall hE)) (hw u)
  have heq : (∑ d ∈ M, sourceShiftTwoNonunitMass r₀ Ψ L d / (d.totient : ℝ)) =
      ∑ u ∈ S, w u * (∑ d ∈ M, if ¬u.Coprime d then (d.totient : ℝ)⁻¹ else 0) := by
    unfold sourceShiftTwoNonunitMass
    simp_rw [Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : u.Coprime d <;> simp [ZMod.isUnit_iff_coprime, hc, w, div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ ∑ u ∈ S, w u * (K * sourceSquarefreeTotientSum N) := Finset.sum_le_sum hpoint
    _ = ((4 / Real.log 2) * L / L^20 * sourceSquarefreeTotientSum N) *
        sourceOriginalXA r₀
          (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
          (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
      rw [← Finset.sum_mul]
      change (∑ u ∈ S, w u) * (K * sourceSquarefreeTotientSum N) = _
      unfold sourceOriginalXA
      change (∑ u ∈ S, w u) * (K * sourceSquarefreeTotientSum N) =
        (K * sourceSquarefreeTotientSum N) * (∑ u ∈ S, w u)
      ring


/- The genuinely summable principal correction in the ORIGINAL growing
odd squarefree range. No character, TI2, correlation or Mertens input. -/



/- Exact source owner: SourceShiftTwoNonunitSaving.lean; original line 85. -/
theorem source_shift_two_nonunit_full_range_saving
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (hΨ : ∀ t, 0 ≤ Ψ t)
    (θ : ℝ) (hθ : 0 < θ) (hθupper : θ < 1/2) :
    ∀ᶠ L : ℝ in atTop,
      (∑ d ∈ (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d),
        sourceShiftTwoNonunitMass r₀ Ψ L d / (d.totient : ℝ)) ≤
      (4 * Real.exp 1 / Real.log 2) *
        sourceOriginalXA r₀
          (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
          (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ * L^(-18 : ℝ) := by
  filter_upwards [source_shift_two_nonunit_full_range_harmonic r₀ hr₀ Ψ hΨ θ,
    eventually_ge_atTop (2 : ℝ)] with L hbound hL
  dsimp only at hbound
  have hL0 : 0 < L := by linarith
  have hXA : 0 ≤ sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ :=
    source_original_XA_nonneg _ _ _ _ _ hΨ
  have hH := source_squarefree_totient_sum_power_cutoff L θ hL hθ hθupper.le
  have hK : 0 ≤ (4 / Real.log 2) * L / L^20 := by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hcomp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH hK) hXA
  apply hbound.trans
  convert hcomp using 1
  have hrpow : L^(-18 : ℝ) = (L^18)⁻¹ := by
    rw [Real.rpow_neg hL0.le]
    congr 1
    norm_num
  rw [hrpow]
  field_simp [hL0.ne']
  <;> ring



/- Exact source owner: SourceShiftTwoCongruencePrincipalDischarged.lean; original line 10. -/
theorem source_shift_two_genuine_remainder_principal_discharged
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (hΨ : ∀ t, 0 ≤ Ψ t)
    (θ : ℝ) (hθ : 0 < θ) (hθupper : θ < 1/2) :
    ∀ᶠ L : ℝ in atTop,
      let M := (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d)
      (∑ d ∈ M, |sourceShiftTwoRemainder r₀ Ψ L d|) ≤
        (∑ d ∈ M, sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ)) +
        (4 * Real.exp 1 / Real.log 2) *
          sourceOriginalXA r₀
            (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
            (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ * L^(-18 : ℝ) := by
  filter_upwards [source_shift_two_nonunit_full_range_saving
    r₀ hr₀ Ψ hΨ θ hθ hθupper] with L hnonunit
  dsimp only
  have hrem := source_shift_two_actual_range_remainder_sum r₀ Ψ L θ hΨ
  dsimp only at hrem
  exact hrem.trans (add_le_add (le_refl _) hnonunit)



/- Exact source owner: SourceShiftTwoConditionalCongruence.lean; original line 26. -/
theorem source_original_SW_congruence_input
    (hSW : SourcePrimeSiegelWalfisz) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (hnon : ∀ t, 0 ≤ Ψ t) : SourceShiftTwoCongruenceInput r₀ Ψ := by
  intro θ D hθ hθu hD
  obtain ⟨C,hC,hbound⟩ := source_original_SW_Echi_saving hSW r₀ hr₀ Ψ hΨ hs θ D hθ hθu hD
  let c₀ : ℝ := 4*Real.exp 1/Real.log 2
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨C+c₀,by positivity,?_⟩
  filter_upwards [hbound,source_shift_two_genuine_remainder_principal_discharged
    r₀ hr₀ Ψ hnon θ hθ hθu,eventually_gt_atTop (0:ℝ)] with L hc hr hL
  dsimp only at hr
  have hXA : 0 ≤ sourceOriginalXA r₀
    (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
    (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ :=
    source_original_XA_nonneg _ _ _ _ _ hnon
  have h1 := mul_nonneg hc₀ (by positivity : 0 ≤ Real.exp L*L^(-D))
  have h2 := mul_nonneg hC (mul_nonneg hXA (Real.rpow_nonneg hL.le (-18:ℝ)))
  dsimp [c₀] at h1 h2 ⊢
  nlinarith



/- Exact source owner: SourceSWUnconditionalEchi.lean; original line 23. -/
theorem source_shift_two_congruence_input_unconditional
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (hnon : ∀ t, 0 ≤ Ψ t) : SourceShiftTwoCongruenceInput r₀ Ψ :=
  source_original_SW_congruence_input sourcePrimeSiegelWalfisz_unconditional
    r₀ hr₀ Ψ hΨ hs hnon


end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualSourceBlockSieve -/

section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Exact distinct-prime product divisibility, preserving repeated factors of u. -/
theorem shift_two_prime_product_dvd_iff (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) (u : ℕ) :
    (∏ p ∈ s, p) ∣ u+2 ↔ ∀ p ∈ s, p ∣ u+2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hn ih =>
    have hps : p.Prime := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hps.coprime_iff_not_dvd.mpr
      intro hdiv
      have he : p = q := (Nat.dvd_prime (hs q hq)).mp hdiv |>.resolve_left hps.ne_one
      exact hn (he ▸ hq)
    rw [Finset.prod_insert hn]
    constructor
    · intro h
      have h1 := dvd_trans (dvd_mul_right p (∏ q ∈ s, q)) h
      have h2 := dvd_trans (dvd_mul_left (∏ q ∈ s, q) p) h
      intro q hq
      rcases Finset.mem_insert.mp hq with he | hq
      · simpa [he] using h1
      · exact (ih hs).mp h2 q hq
    · intro h
      have h1 := h p (Finset.mem_insert_self _ _)
      have h2 : ∀ q ∈ s, q ∣ u+2 := fun q hq => h q (Finset.mem_insert_of_mem hq)
      exact hc.mul_dvd_of_dvd_of_dvd h1 ((ih hs).mpr h2)

noncomputable def sourceShiftTwoLocalDensity (d : ℕ) : ℝ :=
  (d.totient : ℝ)⁻¹

noncomputable def sourceShiftTwoBad (P : Finset ℕ) (u : ℕ) : Finset ℕ :=
  P.filter (fun p => p ∣ u+2)

noncomputable def sourceShiftTwoSiftedMass
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2 * Real.exp L⌋₊+1),
    if ∀ p ∈ P, ¬p ∣ u+2 then sourceOriginalMovingWeight r₀ Ψ L u else 0

theorem source_shift_two_local_density_product (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) :
    sourceShiftTwoLocalDensity (∏ p ∈ s, p) =
      ∏ p ∈ s, sourceShiftTwoLocalDensity p := by
        classical
  unfold sourceShiftTwoLocalDensity
  rw [shift_two_totient_prime_product s hp, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp'
  rw [Nat.totient_prime (hp p hp'), Nat.cast_sub (hp p hp').one_le, Nat.cast_one]

/-- Every block-sieve intersection is exactly the genuine shifted residue mass;
its remainder is defined from A, with no assumed distribution conclusion. -/
theorem source_shift_two_exact_block_moment
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (P s : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hs : s ⊆ P) :
    (∑ u ∈ Finset.range (⌊2 * Real.exp L⌋₊+1),
      sourceOriginalMovingWeight r₀ Ψ L u *
        ∏ p ∈ s, if p ∈ sourceShiftTwoBad P u then (1:ℝ) else 0) =
    sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ *
        (∏ p ∈ s, sourceShiftTwoLocalDensity p) +
          sourceShiftTwoRemainder r₀ Ψ L (∏ p ∈ s, p) := by
            classical
  have hIndicator (u : ℕ) :
      (∏ p ∈ s, if p ∈ sourceShiftTwoBad P u then (1:ℝ) else 0) =
        if (∏ p ∈ s, p) ∣ u+2 then 1 else 0 := by
          classical
    calc
      _ = ∏ p ∈ s, if p ∣ u+2 then (1:ℝ) else 0 := by
        classical
        apply Finset.prod_congr rfl
        intro p hps
        simp [sourceShiftTwoBad, hs hps]
      _ = if ∀ p ∈ s, p ∣ u+2 then 1 else 0 := by
        by_cases hi : ∀ p ∈ s, p ∣ u+2
        · rw [if_pos hi]
          exact Finset.prod_eq_one (fun p hps => if_pos (hi p hps))
        · rw [if_neg hi]
          push_neg at hi
          obtain ⟨p,hps,hnd⟩ := hi
          exact Finset.prod_eq_zero hps (if_neg hnd)
      _ = _ := by
        have hi := shift_two_prime_product_dvd_iff s (fun p hps => hp p (hs hps)) u
        by_cases hd : (∏ p ∈ s, p) ∣ u+2
        · rw [if_pos hd, if_pos (hi.mp hd)]
        · have hn : ¬∀ p ∈ s, p ∣ u+2 := fun h => hd (hi.mpr h)
          simp [hd, hn]
  simp_rw [hIndicator]
  have hMass : (∑ u ∈ Finset.range (⌊2 * Real.exp L⌋₊+1),
      sourceOriginalMovingWeight r₀ Ψ L u *
        (if (∏ p ∈ s, p) ∣ u+2 then (1:ℝ) else 0)) =
      sourceShiftTwoDivisorMass r₀ Ψ L (∏ p ∈ s, p) := by
        classical
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hd : (∏ p ∈ s, p) ∣ u+2 <;> simp [sourceShiftTwoDivisorMass, hd]
  rw [hMass, ← source_shift_two_local_density_product s (fun p hps => hp p (hs hps))]
  unfold sourceShiftTwoRemainder sourceShiftTwoLocalDensity
  rw [div_eq_mul_inv]
  ring

/-- Exact source-weight specialization of the two-sided block sieve.
The error uses the shifted source remainder; every constant and the level
are kept explicit, including the h=2 case. No Type II theorem is assumed. -/
theorem source_shift_two_block_sieve
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L z C : ℝ)
    (J h : ℕ) (blocks : Fin J → Finset ℕ)
    (hz : 1 < z) (hh : 2 ≤ h) (heven : Even h) (hC : 0 ≤ C)
    (hΨ : ∀ t, 0 ≤ Ψ t)
    (hp : ∀ j p, p ∈ blocks j → p.Prime ∧ 3 ≤ p ∧
      z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧ (p:ℝ) ≤ z^((1/2:ℝ)^j.val))
    (hblock : ∀ j, (∑ p ∈ blocks j, sourceShiftTwoLocalDensity p) ≤ C) :
    let P := Finset.univ.biUnion blocks
    let XA := sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ
    let V₁ := ∏ p ∈ P, (1-sourceShiftTwoLocalDensity p)
    let ρ := ((Real.exp (Real.exp 1*C)/(1-Real.exp (-1)))/Real.exp (-C/(1/2))) * Real.exp (-(h:ℝ))
    let E := ∑ d ∈ ((∏ p ∈ P, p).divisors.filter
      (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ z^(4*(h:ℝ)+2))),
        |sourceShiftTwoRemainder r₀ Ψ L d|
    XA*V₁*(1-ρ*Real.exp ρ)-E ≤ sourceShiftTwoSiftedMass r₀ Ψ L P ∧
      sourceShiftTwoSiftedMass r₀ Ψ L P ≤ XA*V₁*Real.exp ρ+E := by
        classical
  dsimp only
  let P := Finset.univ.biUnion blocks
  have hP : ∀ p ∈ P, p.Prime := by
    classical
    intro p hpm
    obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp hpm
    exact (hp j p hpj).1
  have hg : ∀ j p, p ∈ blocks j →
      0 ≤ sourceShiftTwoLocalDensity p ∧ sourceShiftTwoLocalDensity p ≤ 1-(1/2:ℝ) := by
        classical
    intro j p hpj
    have hprime := (hp j p hpj).1
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast (hp j p hpj).2.1
    have hg : sourceShiftTwoLocalDensity p = ((p:ℝ)-1)⁻¹ := by
      classical
      simp [sourceShiftTwoLocalDensity, Nat.totient_prime hprime, Nat.cast_sub hprime.one_le]
    rw [hg, inv_eq_one_div]
    have hpos : 0 < (p:ℝ)-1 := by linarith
    constructor
    · exact div_nonneg (by norm_num) hpos.le
    · apply (div_le_iff₀ hpos).mpr
      nlinarith
  have hS : (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      sourceOriginalMovingWeight r₀ Ψ L u *
        (if ∀ j, blocks j ∩ sourceShiftTwoBad P u = ∅ then (1:ℝ) else 0)) =
        sourceShiftTwoSiftedMass r₀ Ψ L P := by
          classical
    unfold sourceShiftTwoSiftedMass
    apply Finset.sum_congr rfl
    intro u hu
    have hi : (∀ j, blocks j ∩ sourceShiftTwoBad P u = ∅) ↔
        ∀ p ∈ P, ¬p ∣ u+2 := by
          classical
      constructor
      · intro h p hpm hdiv
        obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp hpm
        have hm : p ∈ blocks j ∩ sourceShiftTwoBad P u := by
          classical
          simp [hpj, sourceShiftTwoBad, hpm, hdiv]
        rw [h j] at hm
        exact Finset.notMem_empty _ hm
      · intro h j
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hpm
        have hm := Finset.mem_inter.mp hpm
        have hb := Finset.mem_filter.mp hm.2
        exact h p hb.1 hb.2
    rw [if_congr hi rfl rfl]
    by_cases h : ∀ p ∈ P, ¬p ∣ u+2 <;> simp [h]
  have hresult := Green64Analytic.SieveContinuation.weighted_block_sieve
    h J blocks z C (1/2) (Finset.range (⌊2*Real.exp L⌋₊+1))
    (sourceOriginalMovingWeight r₀ Ψ L) (sourceShiftTwoBad P)
    sourceShiftTwoLocalDensity (sourceShiftTwoRemainder r₀ Ψ L)
    (sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ)
    hz hh heven hC (by norm_num)
    (source_original_XA_nonneg _ _ _ _ _ hΨ)
    (fun u hu => mul_nonneg (source_original_parity_pointwise _ _ _ _).1 (hΨ _))
    (fun j p hpj => ⟨(hp j p hpj).1,(hp j p hpj).2.2⟩) hg hblock
    (fun s hs => source_shift_two_exact_block_moment r₀ Ψ L P s hP hs)
  dsimp only at hresult
  rw [hS] at hresult
  exact hresult

end Green64Analytic.SourceBlockSieve

end

