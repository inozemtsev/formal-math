module

public import Green64.Library.Weights.Part105
public import Green64.Library.Weights.ParityLiteralParityTarget
public import Green64.Library.Weights.Part104

@[expose] public section

/-!
# Weights / Part106

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Mass008 -/

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
open Filter Topology Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoFreeCutoffWindow.lean; original line 11. -/
theorem source_original_cutoff_on_free_prime_window
    (x α β c : ℝ) (n : ℕ) (Ψ : ℝ → ℝ)
    (hx : 0 < x) (hn : 0 < n)
    (hα : 0 < α) (hαβ : α < β)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ p ∈ sourceFreePrimeWindow
        (Real.log (α*x/(n:ℝ))) (Real.log (β/α)),
      c ≤ Ψ (((p:ℝ)*(n:ℝ))/x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hβ : 0 < β := hα.trans hαβ
  have hT : 0 < α*x/(n:ℝ) := by positivity
  have hS : 0 < β/α := div_pos hβ hα
  have hUpperEq :
      Real.exp (Real.log (α*x/(n:ℝ)) + Real.log (β/α)) =
        β*x/(n:ℝ) := by
    rw [Real.exp_add, Real.exp_log hT, Real.exp_log hS]
    field_simp
    <;> ring
  intro p hp
  have hRange := (Finset.mem_filter.mp hp).1
  have hpp := Finset.mem_Ioc.mp hRange
  have hnLower : (⌊Real.exp (Real.log (α*x/(n:ℝ)))⌋₊:ℝ)+1 ≤
      (p:ℝ) := by exact_mod_cast hpp.1
  have hnFloor := Nat.lt_floor_add_one (Real.exp (Real.log (α*x/(n:ℝ))))
  have hpLow : α*x/(n:ℝ) ≤ (p:ℝ) := by
    calc
      α*x/(n:ℝ) = Real.exp (Real.log (α*x/(n:ℝ))) :=
        (Real.exp_log hT).symm
      _ ≤ (⌊Real.exp (Real.log (α*x/(n:ℝ)))⌋₊:ℝ)+1 := hnFloor.le
      _ ≤ (p:ℝ) := hnLower
  have hpUpper' : (p:ℝ) ≤
      (⌊Real.exp (Real.log (α*x/(n:ℝ)) + Real.log (β/α))⌋₊:ℝ) :=
    by exact_mod_cast hpp.2
  have hpUpper : (p:ℝ) ≤ β*x/(n:ℝ) := by
    calc
      (p:ℝ) ≤ (⌊Real.exp (Real.log (α*x/(n:ℝ)) + Real.log (β/α))⌋₊:ℝ) := hpUpper'
      _ ≤ Real.exp (Real.log (α*x/(n:ℝ)) + Real.log (β/α)) :=
        Nat.floor_le (Real.exp_nonneg _)
      _ = β*x/(n:ℝ) := hUpperEq
  have hnScale : 0 ≤ (n:ℝ)/x := (div_pos hnR hx).le
  have hLower : α ≤ ((p:ℝ)*(n:ℝ))/x := by
    have h := mul_le_mul_of_nonneg_right hpLow hnScale
    have hEq : (α*x/(n:ℝ))*((n:ℝ)/x) = α := by
      field_simp
    rw [hEq] at h
    simpa only [mul_div_assoc] using h
  have hHigher : ((p:ℝ)*(n:ℝ))/x ≤ β := by
    have h := mul_le_mul_of_nonneg_right hpUpper hnScale
    have hEq : (β*x/(n:ℝ))*((n:ℝ)/x) = β := by
      field_simp
    rw [hEq] at h
    simpa only [mul_div_assoc] using h
  exact hΨ _ hLower hHigher



/- Exact source owner: SourceShiftTwoPositiveCutoffMass.lean; original line 12. -/
theorem source_free_slot_cutoff_mass_uniform
    (a M α β c : ℝ) (Ψ : ℝ → ℝ)
    (ha : 0 < a) (haM : a ≤ M)
    (hα : 0 < α) (hαβ : α < β) (hc : 0 ≤ c)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, 0 < n →
      a ≤ Real.log (α*Real.exp L/(n:ℝ))/L →
      Real.log (α*Real.exp L/(n:ℝ))/L ≤ M →
      c*Real.log (β/α)/(4*M*L) ≤
        ∑ p ∈ sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α)),
          (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) := by
  have hratio : (1:ℝ) < β/α :=
    (lt_div_iff₀ hα).mpr (by simpa using hαβ)
  have hh : 0 < Real.log (β/α) := Real.log_pos hratio
  have hUn := source_free_prime_window_uniform a M
    (Real.log (β/α)) ha haM hh
  filter_upwards [hUn, eventually_gt_atTop (0:ℝ)]
    with L hUL hL n hn hlow hhigh
  let ell : ℝ := Real.log (α*Real.exp L/(n:ℝ))
  let h : ℝ := Real.log (β/α)
  have hEq : (ell/L)*L = ell := by
    dsimp [ell]
    field_simp
  have hWin := hUL (ell/L) hlow hhigh
  rw [hEq] at hWin
  rw [source_free_window_reciprocal_eq] at hWin
  have hCut := source_original_cutoff_on_free_prime_window
    (Real.exp L) α β c n Ψ (Real.exp_pos _) hn hα hαβ hΨ
  have hSum : c*(∑ p ∈ sourceFreePrimeWindow ell h, (p:ℝ)⁻¹) ≤
      ∑ p ∈ sourceFreePrimeWindow ell h,
         (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpPsi : c ≤ Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) := by
      simpa only [ell, h] using hCut p hp
    calc
      c*(p:ℝ)⁻¹ = (p:ℝ)⁻¹*c := by ring
      _ ≤ (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) :=
        mul_le_mul_of_nonneg_left hpPsi (by positivity)
  have hCompare : c*(h/(4*M*L)) ≤
      c*(∑ p ∈ sourceFreePrimeWindow ell h, (p:ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hWin hc
  have hFinal := hCompare.trans hSum
  simpa only [ell, h, mul_div_assoc] using hFinal



/- Exact source owner: SourceShiftTwoQ0CutoffFloor.lean; original line 12. -/
theorem source_original_Q0_cutoff_free_slot_floor
    (s δ α β c : ℝ) (Ψ : ℝ → ℝ)
    (hs : 0 < s) (hδ : 0 < δ) (hδsmall : δ ≤ s/5)
    (hα : 0 < α) (hαβ : α < β) (hc : 0 ≤ c)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, 0 < n →
      s ≤ Real.log (α*Real.exp L/(n:ℝ))/L →
      Real.log (α*Real.exp L/(n:ℝ))/L ≤ (6/5:ℝ)*s-δ →
      c*Real.log (β/α)/(4*((6/5:ℝ)*s-δ)*L) ≤
        ∑ p ∈ sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α)),
          (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) ∧
      sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α))
        ⊆ sourceClosedPrimeLogBand L s ((6/5:ℝ)*s) := by
  let M : ℝ := (6/5:ℝ)*s-δ
  have hsM : s ≤ M := by
    dsimp [M]
    nlinarith
  have hαratio : (1:ℝ) < β/α :=
    (lt_div_iff₀ hα).mpr (by simpa using hαβ)
  have hh : 0 < Real.log (β/α) := Real.log_pos hαratio
  have hFin := source_free_slot_cutoff_mass_uniform
    s M α β c Ψ hs hsM hα hαβ hc hΨ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  filter_upwards [hFin, eventually_gt_atTop (0:ℝ),
      eventually_ge_atTop (Real.log (β/α)/δ)]
    with L hFL hL hLong n hn hl hr
  let ell : ℝ := Real.log (α*Real.exp L/(n:ℝ))
  let h : ℝ := Real.log (β/α)
  have hδL : h ≤ δ*L := by
    calc
      h = δ*(h/δ) := by field_simp
      _ ≤ δ*L := mul_le_mul_of_nonneg_left hLong hδ.le
  have hLeft : s*L ≤ ell := (le_div_iff₀ hL).mp hl
  have hRight : ell ≤ M*L := (div_le_iff₀ hL).mp hr
  have hTop : ell+h ≤ (6/5:ℝ)*s*L := by
    calc
      ell+h ≤ M*L+δ*L := add_le_add hRight hδL
      _ = (6/5:ℝ)*s*L := by dsimp [M]; ring
  have hSubset := source_free_prime_window_subset_original_Q0
    L s ell h hLeft hTop
  refine ⟨?_, ?_⟩
  · exact hFL n hn hl hr
  · simpa only [ell, h] using hSubset



/- Exact source owner: SourceOriginalQ0GoodRestGeometry.lean; original line 15. -/
theorem source_original_Q0_good_rest_window_geometry
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (L α : ℝ) (hL : 0 < L) (hα : 1 ≤ α)
    (n : ℕ) (hn : 0 < n)
    (hRestLo :
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ))
    (hRestHi :
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30)
    (hLogAlpha :
      Real.log α ≤ sourceOriginalQ0Scale r₀*L/30) :
    sourceOriginalQ0Scale r₀ ≤
      Real.log (α*Real.exp L/(n:ℝ))/L ∧
    Real.log (α*Real.exp L/(n:ℝ))/L ≤
      (6/5:ℝ)*sourceOriginalQ0Scale r₀-
        sourceOriginalQ0Scale r₀/30 := by
  let s := sourceOriginalQ0Scale r₀
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 < s := by dsimp [s,sourceOriginalQ0Scale]; positivity
  have hαp : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have hαlog : 0 ≤ Real.log α := Real.log_nonneg hα
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hLogIdentity :
      Real.log (α*Real.exp L/(n:ℝ)) =
        Real.log α + L - Real.log (n:ℝ) := by
    rw [Real.log_div
      (mul_ne_zero (ne_of_gt hαp) (ne_of_gt (Real.exp_pos L)))
      (ne_of_gt hnp),
      Real.log_mul (ne_of_gt hαp) (ne_of_gt (Real.exp_pos L)),
      Real.log_exp]
  have hLow : s*L ≤ Real.log α + L - Real.log (n:ℝ) := by
    dsimp only [s] at hRestHi ⊢
    nlinarith [mul_pos hs hL]
  have hHigh :
      Real.log α + L - Real.log (n:ℝ) ≤
        ((6/5:ℝ)*s-s/30)*L := by
    dsimp only [s] at hRestLo hLogAlpha ⊢
    nlinarith [hRestLo,hLogAlpha]
  rw [hLogIdentity]
  constructor
  · exact (le_div_iff₀ hL).2 hLow
  · exact (div_le_iff₀ hL).2 (by nlinarith [hHigh])



/- Exact source owner: SourceOriginalQ0GoodRestCutoff.lean; original line 11. -/
theorem source_original_Q0_good_rest_cutoff_floor
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hc : 0 ≤ c)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, 0 < n →
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ) →
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30 →
      c*Real.log (β/α)/
        (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
          sourceOriginalQ0Scale r₀/30)*L) ≤
        ∑ p ∈ sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α)),
          (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) ∧
      sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α))
        ⊆ sourceClosedPrimeLogBand L
          (sourceOriginalQ0Scale r₀)
          ((6/5:ℝ)*sourceOriginalQ0Scale r₀) := by
  let s := sourceOriginalQ0Scale r₀
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 < s := by dsimp [s, sourceOriginalQ0Scale]; positivity
  have hδ : 0 < s/30 := by positivity
  have hδsmall : s/30 ≤ s/5 := by nlinarith
  have hCutoff := source_original_Q0_cutoff_free_slot_floor
    s (s/30) α β c Ψ hs hδ hδsmall
    (by linarith : 0 < α) hαβ hc hΨ
  have hLarge : ∀ᶠ L : ℝ in atTop,
      Real.log α/(s/30) ≤ L :=
    eventually_ge_atTop _
  filter_upwards [hCutoff, eventually_gt_atTop (0:ℝ), hLarge]
    with L hCutoffL hL hLargeL
  intro n hn hRestLo hRestHi
  have hLogAlpha : Real.log α ≤ s*L/30 := by
    have hh := (div_le_iff₀ hδ).mp hLargeL
    dsimp only [s]
    nlinarith
  have hWindow := source_original_Q0_good_rest_window_geometry
    r₀ hr₀ L α hL hα.le n hn hRestLo hRestHi hLogAlpha
  simpa only [s] using hCutoffL n hn hWindow.1 hWindow.2



/- Exact source owner: SourceQ0FreePrimeCountBridge.lean; original line 10. -/
theorem source_original_free_prime_count_from_reciprocals
    (x α β : ℝ) (n : ℕ) (Ψ : ℝ → ℝ)
    (hx : 0 < x) (hα : 0 < α) (hn : 0 < n)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t) :
    (α*x/(n:ℝ)) *
      (∑ p ∈ sourceFreePrimeWindow
         (Real.log (α*x/(n:ℝ))) (Real.log (β/α)),
         (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/x)) ≤
      ∑ p ∈ sourceFreePrimeWindow
         (Real.log (α*x/(n:ℝ))) (Real.log (β/α)),
         Ψ (((p:ℝ)*(n:ℝ))/x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hT : 0 < α*x/(n:ℝ) := by positivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpR : (0:ℝ) < p := by exact_mod_cast hPrime.pos
  have hprange := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hpF : (⌊Real.exp (Real.log (α*x/(n:ℝ)))⌋₊:ℝ)+1 ≤
      (p:ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hprange.1)
  have hplow : α*x/(n:ℝ) ≤ (p:ℝ) := by
    calc
      α*x/(n:ℝ) = Real.exp (Real.log (α*x/(n:ℝ))) :=
        (Real.exp_log hT).symm
      _ ≤ (⌊Real.exp (Real.log (α*x/(n:ℝ)))⌋₊:ℝ)+1 :=
        (Nat.lt_floor_add_one _).le
      _ ≤ (p:ℝ) := hpF
  have hdiv : (α*x/(n:ℝ))/(p:ℝ) ≤ 1 :=
    (div_le_iff₀ hpR).mpr (by linarith)
  calc
    (α*x/(n:ℝ)) *
        ((p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/x)) =
      ((α*x/(n:ℝ))/(p:ℝ)) * Ψ (((p:ℝ)*(n:ℝ))/x) := by ring
    _ ≤ 1 * Ψ (((p:ℝ)*(n:ℝ))/x) :=
      mul_le_mul_of_nonneg_right hdiv (hΨnonneg _)
    _ = Ψ (((p:ℝ)*(n:ℝ))/x) := by ring



/- Exact source owner: SourceQ0GoodRestPrimeCount.lean; original line 11. -/
theorem source_original_Q0_good_rest_prime_count_floor
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hc : 0 ≤ c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, 0 < n →
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ) →
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30 →
      (α*Real.exp L/(n:ℝ)) *
        (c*Real.log (β/α)/
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L)) ≤
      ∑ p ∈ sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α)),
          Ψ (((p:ℝ)*(n:ℝ))/Real.exp L) := by
  have hGood := source_original_Q0_good_rest_cutoff_floor
    r₀ hr₀ α β c Ψ hα hαβ hc hΨ
  filter_upwards [hGood] with L hGoodL
  intro n hn hRestLo hRestHi
  have hHarm := (hGoodL n hn hRestLo hRestHi).1
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hαR : 0 < α := by linarith
  have hfac : 0 ≤ α*Real.exp L/(n:ℝ) := by positivity
  have hCount := source_original_free_prime_count_from_reciprocals
    (Real.exp L) α β n Ψ (Real.exp_pos _) hαR hn hΨnonneg
  calc
    (α*Real.exp L/(n:ℝ)) *
        (c*Real.log (β/α)/
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L)) ≤
      (α*Real.exp L/(n:ℝ)) *
        (∑ p ∈ sourceFreePrimeWindow
          (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α)),
          (p:ℝ)⁻¹ * Ψ (((p:ℝ)*(n:ℝ))/Real.exp L)) :=
        mul_le_mul_of_nonneg_left hHarm hfac
    _ ≤ _ := hCount



/- Exact source owner: SourceOriginalQ0WindowCutoffCount.lean; original line 11. -/
theorem source_original_free_Q0_window_within_u_cutoff
    (x α β : ℝ) (n : ℕ) (p : ℕ)
    (hx : 0 < x) (hα : 0 < α) (hαβ : α < β) (hβ : β < 2)
    (hn : 0 < n)
    (hp : p ∈ sourceFreePrimeWindow
      (Real.log (α*x/(n:ℝ))) (Real.log (β/α))) :
    p*n < ⌊2*x⌋₊+1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hβp : 0 < β := hα.trans hαβ
  have hT : 0 < α*x/(n:ℝ) := by positivity
  have hS : 0 < β/α := div_pos hβp hα
  have hUpperEq :
      Real.exp (Real.log (α*x/(n:ℝ)) + Real.log (β/α)) =
        β*x/(n:ℝ) := by
    rw [Real.exp_add, Real.exp_log hT, Real.exp_log hS]
    field_simp
  have hpp := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hUpper : (p:ℝ) ≤ β*x/(n:ℝ) := by
    calc
      (p:ℝ) ≤ (⌊Real.exp (Real.log (α*x/(n:ℝ)) +
        Real.log (β/α))⌋₊:ℝ) := by exact_mod_cast hpp.2
      _ ≤ Real.exp (Real.log (α*x/(n:ℝ)) +
        Real.log (β/α)) := Nat.floor_le (Real.exp_nonneg _)
      _ = β*x/(n:ℝ) := hUpperEq
  have hpn : ((p*n:ℕ):ℝ) ≤ β*x := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right hUpper hnR.le
    have hs : (β*x/(n:ℝ))*(n:ℝ) = β*x := by field_simp
    nlinarith
  have hlt : ((p*n:ℕ):ℝ) ≤ 2*x := by
    nlinarith [mul_lt_mul_of_pos_right hβ hx]
  exact Nat.lt_succ_of_le (Nat.le_floor hlt)

/- The original free-Q0 lower prime count remains valid inside
both the TRUE Q0 band and the actual finite-u cutoff of X_A. -/



/- Exact source owner: SourceOriginalQ0WindowCutoffCount.lean; original line 46. -/
theorem source_original_Q0_good_rest_count_with_u_cutoff
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, 0 < n →
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ) →
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30 →
      (α*Real.exp L/(n:ℝ)) *
        (c*Real.log (β/α)/
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L)) ≤
      ∑ p ∈ sourceClosedPrimeLogBand L
          (sourceOriginalQ0Scale r₀)
          ((6/5:ℝ)*sourceOriginalQ0Scale r₀),
        if p*n < ⌊2*Real.exp L⌋₊+1
        then Ψ ((((p*n:ℕ):ℝ))/Real.exp L) else 0 := by
  have hCount := source_original_Q0_good_rest_prime_count_floor
    r₀ hr₀ α β c Ψ hα hαβ hc hΨnonneg hΨ
  have hWindow := source_original_Q0_good_rest_cutoff_floor
    r₀ hr₀ α β c Ψ hα hαβ hc hΨ
  filter_upwards [hCount,hWindow] with L hCountL hWindowL
  intro n hn hLo hHi
  let s := sourceOriginalQ0Scale r₀
  let w := sourceFreePrimeWindow
     (Real.log (α*Real.exp L/(n:ℝ))) (Real.log (β/α))
  let Q0 := sourceClosedPrimeLogBand L s ((6/5:ℝ)*s)
  have hSubset : w ⊆ Q0 := (hWindowL n hn hLo hHi).2
  have hCountLower := hCountL n hn hLo hHi
  have hWinLe :
      (∑ p ∈ w, Ψ (((p:ℝ)*(n:ℝ))/Real.exp L)) ≤
      ∑ p ∈ Q0,
        if p*n < ⌊2*Real.exp L⌋₊+1
        then Ψ ((((p*n:ℕ):ℝ))/Real.exp L) else 0 := by
    calc
      _ = ∑ p ∈ w,
          (if p*n < ⌊2*Real.exp L⌋₊+1
          then Ψ ((((p*n:ℕ):ℝ))/Real.exp L) else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hCut := source_original_free_Q0_window_within_u_cutoff
              (Real.exp L) α β n p (Real.exp_pos _) (by linarith)
              hαβ hβ hn hp
            simp [hCut, Nat.cast_mul]
      _ ≤ ∑ p ∈ Q0,
          (if p*n < ⌊2*Real.exp L⌋₊+1
          then Ψ ((((p*n:ℕ):ℝ))/Real.exp L) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
            intro p hpQ hpNot
            split_ifs <;> [exact hΨnonneg _; exact le_refl 0]
  exact hCountLower.trans hWinLe



/- Exact source owner: SourceOriginalQPSplitProduct.lean; original line 9. -/
theorem source_original_Q_product_split_one
    {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (f : I → ℕ) :
    (∏ k : I, f k) = f i * ∏ k : {k : I // k ≠ i}, f k.val := by
  classical
  calc
    (∏ k : I, f k) =
        f i * ∏ k ∈ (Finset.univ.erase i), f k :=
          (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)).symm
    _ = f i * ∏ k : {k : I // k ≠ i}, f k.val := by
      rw [Finset.prod_subtype (p := fun k : I => k ≠ i)
        (Finset.univ.erase i) (by intro k; simp) f]

/- The original full labelled Q product is exactly the free prime
p times the product of every other labelled Q slot. -/



/- Exact source owner: SourceOriginalQPSplitProduct.lean; original line 24. -/
theorem source_original_Q_free_slot_product_exact
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (p : {p // p ∈ Q b})
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1}) :
    (∏ j : B, ∏ m : Fin r,
      (((sourceOriginalQSlotsCurryEquiv r Q)
        ((Equiv.piSplitAt (b,i)
          (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
          (p,rest))) j m).val) =
      p.val * ∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val := by
  classical
  let g := ((Equiv.piSplitAt (b,i)
    (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  have hFree : (g (b,i)).val = p.val := by
    simp [g, Equiv.piSplitAt]
  have hRest : ∀ k : {k : B × Fin r // k ≠ (b,i)},
      (g k.val).val = (rest k).val := by
    intro k
    simp [g, Equiv.piSplitAt, k.property]
  change (∏ j : B, ∏ m : Fin r, (g (j,m)).val) = _
  have hReindex : (∏ j : B, ∏ m : Fin r, (g (j,m)).val) =
      ∏ k : B × Fin r, (g k).val :=
    (Fintype.prod_prod_type (fun k : B × Fin r => (g k).val)).symm
  rw [hReindex]
  rw [source_original_Q_product_split_one (b,i) (fun k => (g k).val)]
  rw [hFree]
  congr 1
  exact Finset.prod_congr rfl (fun k hk => hRest k)



/- Exact source owner: SourceOriginalQPFreePrimeFactor.lean; original line 11. -/
theorem source_original_XA_QP_free_prime_term_factor
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    let n : ℕ :=
      (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) * R.val
    let C : ℝ :=
      (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 - (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)
    (∑ p : {p // p ∈ Q b},
      let f := (sourceOriginalQSlotsCurryEquiv r Q)
        ((Equiv.piSplitAt (b,i)
          (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
      if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
      then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0) =
    C * (∑ p ∈ Q b,
      if p*n < ⌊2*x⌋₊+1
      then Ψ (((p*n:ℕ):ℝ)/x) else 0) := by
  classical
  intro n C
  let f (p : {p // p ∈ Q b}) :=
    (sourceOriginalQSlotsCurryEquiv r Q)
      ((Equiv.piSplitAt (b,i)
        (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  have hprod (p : {p // p ∈ Q b}) :
      (∏ j : B, ∏ m : Fin r, (f p j m).val) * R.val =
        p.val*n := by
    rw [source_original_Q_free_slot_product_exact r Q b i p rest]
    dsimp [n]
    ring
  have hterm (p : {p // p ∈ Q b}) :
      sourceOriginalQPLiteralTerm r Q P x Ψ (f p) R =
        C * Ψ ((((p.val*n:ℕ):ℝ))/x) := by
    unfold sourceOriginalQPLiteralTerm
    rw [source_original_Q_free_slot_product_exact r Q b i p rest]
    rw [show (p.val *
      (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val)) * R.val =
      p.val*n by dsimp [n]; ring]
  calc
    _ = ∑ p : {p // p ∈ Q b},
      C * (if p.val*n < ⌊2*x⌋₊+1
        then Ψ ((((p.val*n:ℕ):ℝ))/x) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          change (if (∏ j : B, ∏ m : Fin r, (f p j m).val) *
            R.val < ⌊2*x⌋₊+1
            then sourceOriginalQPLiteralTerm r Q P x Ψ (f p) R
            else 0) = _
          rw [hprod p, hterm p]
          split_ifs <;> ring
    _ = C * ∑ p : {p // p ∈ Q b},
        (if p.val*n < ⌊2*x⌋₊+1
         then Ψ ((((p.val*n:ℕ):ℝ))/x) else 0) := by
           rw [Finset.mul_sum]
    _ = C * (∑ p ∈ Q b,
        if p*n < ⌊2*x⌋₊+1
        then Ψ (((p*n:ℕ):ℝ)/x) else 0) := by
          exact congrArg (fun y : ℝ => C*y)
            (Finset.sum_coe_sort (Q b) (fun p : ℕ =>
              if p*n < ⌊2*x⌋₊+1
              then Ψ (((p*n:ℕ):ℝ)/x) else 0))



/- Exact source owner: SourceOriginalQ0ActualXALower.lean; original line 13. -/
theorem source_original_Q0_actual_XA_free_prime_floor_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
      (Q : B → Finset ℕ) (P : G → Finset ℕ)
      (b : B) (i : Fin r₀)
      (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
      (hQ0 : Q b = sourceClosedPrimeLogBand L
        (sourceOriginalQ0Scale r₀)
        ((6/5:ℝ)*sourceOriginalQ0Scale r₀))
      (rest : (k : {k : B × Fin r₀ // k ≠ (b,i)}) →
            {p // p ∈ Q k.1.1})
      (R : sourceOriginalPSupported (Finset.univ.biUnion P)),
      let n : ℕ :=
        (∏ k : {k : B × Fin r₀ // k ≠ (b,i)}, (rest k).val) * R.val
      let C : ℝ :=
        (∏ _b : B, (1:ℝ)/(r₀.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 - (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ) →
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30 →
      C * ((α*Real.exp L/(n:ℝ)) *
        (c*Real.log (β/α)/
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L))) ≤
      ∑ p : {p // p ∈ Q b},
        let f := (sourceOriginalQSlotsCurryEquiv r₀ Q)
          ((Equiv.piSplitAt (b,i)
            (fun k : B × Fin r₀ => {p // p ∈ Q k.1})).symm (p,rest))
        if (∏ j : B, ∏ m : Fin r₀, (f j m).val) * R.val <
            ⌊2*Real.exp L⌋₊+1
        then sourceOriginalQPLiteralTerm r₀ Q P (Real.exp L) Ψ f R else 0 := by
  have hCount := source_original_Q0_good_rest_count_with_u_cutoff
    r₀ hr₀ α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hCount] with L hCountL
  intro B G hFinB hDecB hFinG Q P b i hQPrime hQ0 rest R n C hLo hHi
  have hRestProd : 0 <
      (∏ k : {k : B × Fin r₀ // k ≠ (b,i)}, (rest k).val) := by
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact (hQPrime k.val.1 _ (rest k).property).ne_zero
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos hRestProd (Nat.pos_of_ne_zero R.property.1)
  have hFloor := hCountL n hn hLo hHi
  rw [← hQ0] at hFloor
  have hParity : 0 ≤
      (1 - (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2 := by
    rcases source_original_parity_projection_zero_or_one
      (Finset.univ.biUnion P) R.val with hh | hh
    · rw [hh]
    · rw [hh]
      norm_num
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) (source_original_W1_nonneg P R.val)) hParity
  have hFactor := source_original_XA_QP_free_prime_term_factor
    r₀ Q P b i (Real.exp L) Ψ rest R
  change C * _ ≤ _
  rw [hFactor]
  exact mul_le_mul_of_nonneg_left hFloor hC



/- Exact source owner: SourceOriginalQRestProductSplit.lean; original line 10. -/
noncomputable def sourceOriginalQRestPartialProduct
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (keep : B → Prop)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1}) : ℕ :=
  ∏ k ∈ (Finset.univ.filter (fun k :
    {k : B × Fin r // k ≠ (b,i)} => keep k.val.1)),
      (rest k).val

/- The literal rest-product splits EXACTLY into macro and micro
parts. No Q slot or factorial coefficient disappears. -/



/- Exact source owner: SourceOriginalGoodRestCombination.lean; original line 10. -/
theorem source_original_P_delta_eq_Q0_width
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) :
    sourceOriginalPDelta r₀ L =
      sourceOriginalQ0Scale r₀ * L / 5 := by
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  unfold sourceOriginalPDelta sourceOriginalQ0Scale
  field_simp

/- Original good-event deterministic log budget. If the finite
macro Q-slots lie near their midpoints, the remaining micro Q slots
carry ≤Delta/24, and the actual P-part carries ≤Delta/12, then the
whole rest product lies in the checked free-Q₀ midpoint corridor.
No assumed probability mass is used in this geometry statement. -/



/- Exact source owner: SourceOriginalQMacroDeviationBudget.lean; original line 10. -/
theorem source_original_Q_actual_exponent_le_Q0
    (r₀ j : ℕ) (hr₀ : 1 ≤ r₀) :
    sourceOriginalQActualExponent r₀ j ≤ sourceOriginalQ0Scale r₀ := by
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 ≤ sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    positivity
  have hp : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hpp : (0:ℝ) < (2:ℝ)^j := by positivity
  unfold sourceOriginalQActualExponent
  exact (div_le_iff₀ hpp).mpr (by nlinarith)

/- Deterministic total absolute midpoint error of all restricted
original macro rest slots. Counting them uses the ACTUAL labelled
Q slot index, with one free slot excluded. -/



/- Exact source owner: SourceOriginalQMacroDeviationBudget.lean; original line 26. -/
theorem source_original_Q_actual_macro_error_budget
    (r₀ jₓ k : ℕ) (hr₀ : 1 ≤ r₀)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεBudget : ((k*r₀:ℕ):ℝ)*ε ≤ 1/120)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (err : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)} → ℝ)
    (hErr : ∀ z, z.val.1.val < k →
      err z ≤ ε*sourceOriginalQActualExponent r₀ z.val.1.val*L) :
    (∑ z ∈ ((Finset.univ : Finset
      {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
      (fun z => z.val.1.val < k)), err z) ≤
      sourceOriginalPDelta r₀ L / 24 := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let A : Finset I := Finset.univ.filter
    (fun z => z.val.1.val < k)
  let s : ℝ := sourceOriginalQ0Scale r₀
  have hs : 0 ≤ s := by
    dsimp [s,sourceOriginalQ0Scale]
    have hr : (0:ℝ) < r₀ := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
    positivity
  have hsL : 0 ≤ s*L := mul_nonneg hs hL
  have hPer (z : I) (hz : z ∈ A) : err z ≤ ε*s*L := by
    have hzMacro : z.val.1.val < k := (Finset.mem_filter.mp hz).2
    have hj := source_original_Q_actual_exponent_le_Q0
      r₀ z.val.1.val hr₀
    have hE := hErr z hzMacro
    have hCompare :
      ε*sourceOriginalQActualExponent r₀ z.val.1.val*L ≤ ε*s*L := by
      nlinarith [mul_nonneg hε hL]
    exact hE.trans hCompare
  have hCount : A.card ≤ k*r₀ :=
    source_original_Q_fixed_macro_rest_slot_count r₀ jₓ k b i
  have hN : (A.card:ℝ) ≤ (k*r₀:ℕ) := by
    exact_mod_cast hCount
  have hFull : (∑ z ∈ A, err z) ≤ (A.card:ℝ)*(ε*s*L) := by
    calc
      _ ≤ ∑ _z ∈ A, ε*s*L := by
        apply Finset.sum_le_sum
        intro z hz
        exact hPer z hz
      _ = (A.card:ℝ)*(ε*s*L) := by simp
  have hBound : ((A.card:ℝ)*(ε*s*L)) ≤ s*L/120 := by
    have hNN : 0 ≤ ε*s*L := by positivity
    have hh := mul_le_mul_of_nonneg_right hN hNN
    have hm := mul_le_mul_of_nonneg_right hεBudget hsL
    nlinarith
  have hDelta := source_original_P_delta_eq_Q0_width r₀ L hr₀
  change (∑ z ∈ A, err z) ≤ sourceOriginalPDelta r₀ L/24
  calc
    _ ≤ (A.card:ℝ)*(ε*s*L) := hFull
    _ ≤ s*L/120 := hBound
    _ = sourceOriginalPDelta r₀ L/24 := by
      rw [hDelta]
      ring



/- Exact source owner: SourceOriginalQMidpointLogInterval.lean; original line 9. -/
theorem source_original_Q_closed_prime_log_bounds
    (L u v : ℝ) (p : ℕ)
    (hp : p ∈ sourceClosedPrimeLogBand L u v) :
    u*L ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ v*L := by
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpPos : (0:ℝ) < p := by exact_mod_cast hpPrime.pos
  have hRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hLower : Real.exp (u*L) ≤ (p:ℝ) :=
    (Nat.ceil_le).1 hRange.1
  have hCastUpper : (p:ℝ) ≤ (⌊Real.exp (v*L)⌋₊:ℝ) := by
    exact_mod_cast hRange.2
  have hUpper : (p:ℝ) ≤ Real.exp (v*L) :=
    hCastUpper.trans (Nat.floor_le (Real.exp_nonneg _))
  constructor
  · have hh := Real.log_le_log (Real.exp_pos _) hLower
    rwa [Real.log_exp] at hh
  · have hh := Real.log_le_log hpPos hUpper
    rwa [Real.log_exp] at hh

/- Each actual midpoint prime contributes at most eps*s_j*L
absolute logarithmic deviation from its true manuscript midpoint
m_j=(11/10)*s_j*L. The bound is pointwise, not probabilistic. -/



/- Exact source owner: SourceOriginalQMidpointLogInterval.lean; original line 31. -/
theorem source_original_Q_midpoint_prime_log_deviation
    (r₀ j : ℕ) (hr₀ : 1 ≤ r₀)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (p : ℕ) (hp : p ∈ sourceOriginalQRestrictedMidpoint r₀ j ε L) :
    |Real.log (p:ℝ) - (11/10:ℝ)*
      sourceOriginalQActualExponent r₀ j*L| ≤
      ε*sourceOriginalQActualExponent r₀ j*L := by
  let s : ℝ := sourceOriginalQActualExponent r₀ j
  let u : ℝ := (11/10-ε)*s
  let v : ℝ := (11/10+ε)*s
  have hh : u*L ≤ Real.log (p:ℝ) ∧
      Real.log (p:ℝ) ≤ v*L := by
    exact source_original_Q_closed_prime_log_bounds L u v p
      (source_prime_log_band_subset_closed L u v hp)
  change |Real.log (p:ℝ) - (11/10:ℝ)*s*L| ≤ ε*s*L
  change ((11/10-ε)*s)*L ≤ Real.log (p:ℝ) ∧
    Real.log (p:ℝ) ≤ ((11/10+ε)*s)*L at hh
  apply abs_le.mpr
  constructor
  · nlinarith [hh.1]
  · nlinarith [hh.2]



/- Exact source owner: SourceOriginalQGoodRestMacroBudget.lean; original line 11. -/
theorem source_original_Q_actual_good_rest_macro_deviation
    (r₀ jₓ k : ℕ) (hr₀ : 1 ≤ r₀)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεBudget : ((k*r₀:ℕ):ℝ)*ε ≤ 1/120)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (Q := sourceOriginalQActualBands r₀ jₓ L)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ Q z.val.1})
    (hGood : ∀ z, (rest z).val ∈
      sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i z) :
    (∑ z ∈ ((Finset.univ : Finset
      {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
      (fun z => z.val.1.val < k)),
      |Real.log ((rest z).val:ℝ) -
        (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L|)
      ≤ sourceOriginalPDelta r₀ L/24 := by
  classical
  let err (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) : ℝ :=
    |Real.log ((rest z).val:ℝ) -
      (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L|
  have hBound (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)})
      (hz : z.val.1.val < k) :
      err z ≤ ε*sourceOriginalQActualExponent r₀ z.val.1.val*L := by
    have hMem := hGood z
    have hMemMid : (rest z).val ∈
        sourceOriginalQRestrictedMidpoint r₀ z.val.1.val ε L := by
      dsimp only [sourceOriginalQJointRestAllowed] at hMem
      rwa [if_pos hz] at hMem
    exact source_original_Q_midpoint_prime_log_deviation
      r₀ z.val.1.val hr₀ L ε hL hε (rest z).val hMemMid
  change (∑ z ∈ ((Finset.univ : Finset
    {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
    (fun z => z.val.1.val < k)), err z) ≤
      sourceOriginalPDelta r₀ L/24
  exact source_original_Q_actual_macro_error_budget
    r₀ jₓ k hr₀ L ε hL hε hεBudget b i err hBound



/- Exact source owner: SourceOriginalQGoodMacroProductCenter.lean; original line 9. -/
theorem source_original_Q_actual_good_macro_product_center
    (r₀ jₓ k : ℕ) (hr₀ : 1 ≤ r₀)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεBudget : ((k*r₀:ℕ):ℝ)*ε ≤ 1/120)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
    (hGood : ∀ z, (rest z).val ∈
      sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i z) :
    let A : Finset {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)} :=
      Finset.univ.filter (fun z => z.val.1.val < k)
    |Real.log (((∏ z ∈ A, (rest z).val):ℕ):ℝ) -
      ∑ z ∈ A, (11/10:ℝ)*
        sourceOriginalQActualExponent r₀ z.val.1.val*L| ≤
      sourceOriginalPDelta r₀ L/24 := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let A : Finset I := Finset.univ.filter (fun z => z.val.1.val < k)
  let m (z : I) : ℝ :=
    (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L
  have hp (z : I) (hz : z ∈ A) : ((rest z).val:ℝ) ≠ 0 := by
    have hPrime := source_original_Q_actual_prime
      r₀ jₓ L z.val.1 (rest z).val (rest z).property
    exact_mod_cast hPrime.ne_zero
  have hLog :
      Real.log (((∏ z ∈ A, (rest z).val):ℕ):ℝ) =
      ∑ z ∈ A, Real.log ((rest z).val:ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod hp
  have hBudget := source_original_Q_actual_good_rest_macro_deviation
    r₀ jₓ k hr₀ L ε hL hε hεBudget b i
    (sourceOriginalQActualBands r₀ jₓ L) rest hGood
  change |Real.log (((∏ z ∈ A, (rest z).val):ℕ):ℝ) -
    ∑ z ∈ A, m z| ≤ sourceOriginalPDelta r₀ L/24
  calc
    _ = |∑ z ∈ A, (Real.log ((rest z).val:ℝ) - m z)| := by
      rw [hLog,Finset.sum_sub_distrib]
    _ ≤ ∑ z ∈ A, |Real.log ((rest z).val:ℝ) - m z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ sourceOriginalPDelta r₀ L/24 := hBudget



/- Exact source owner: SourceQRestMacroCenterCore.lean; original line 28. -/
theorem source_original_Q_fin_prefix_sum
    (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℝ) :
    (∑ j : Fin n, if j.val < k then f j.val else 0) =
      ∑ j ∈ Finset.range k, f j := by
  classical
  have hFilter : (Finset.range n).filter (fun j => j < k) =
      Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    (∑ j : Fin n, if j.val < k then f j.val else 0) =
        ∑ j ∈ Finset.range n, if j < k then f j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then f j else 0) n
    _ = ∑ j ∈ (Finset.range n).filter (fun j => j < k), f j := by
      rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range k, f j := by rw [hFilter]



/- Exact source owner: SourceQDyadicGeometryCore.lean; original line 8. -/
theorem source_original_Q_dyadic_half_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((1/2:ℝ)^j)) =
       2 * (1 - (1/2:ℝ)^k) := by
  rw [geom_sum_eq (x := (1/2:ℝ)) (by norm_num) k]
  norm_num
  ring

/- Exact finite shifted dyadic tail, without taking an infinite sum. -/



/- Exact source owner: SourceOriginalQMidpointBudget.lean; original line 11. -/
theorem source_original_Q_ideal_fixed_midpoint_sum
    (r₀ k : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) :
    (∑ j ∈ Finset.range k,
      (r₀:ℝ) * (11/10:ℝ) *
        sourceOriginalQActualExponent r₀ j * L) =
      L * (1 - (1/2:ℝ)^k) := by
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hTerm (j : ℕ) :
      (r₀:ℝ)*(11/10:ℝ)*sourceOriginalQActualExponent r₀ j*L =
      ((r₀:ℝ)*(11/10:ℝ)*sourceOriginalQ0Scale r₀*L) * (1/2:ℝ)^j := by
    have hpow : ((2:ℝ)^j)⁻¹ = (1/2:ℝ)^j := by
      rw [← inv_pow]
      norm_num
    have hscale : sourceOriginalQActualExponent r₀ j =
        sourceOriginalQ0Scale r₀ * (1/2:ℝ)^j := by
      unfold sourceOriginalQActualExponent
      rw [div_eq_mul_inv, hpow]
    rw [hscale]
    ring
  simp_rw [hTerm]
  rw [← Finset.mul_sum, source_original_Q_dyadic_half_sum]
  unfold sourceOriginalQ0Scale
  field_simp
  ring

/- The missing infinite-center logarithm beyond the fixed macro
indices is EXACTLY the first omitted dyadic midpoint tail. -/



/- Exact source owner: SourceQRestMacroCenterCore.lean; original line 9. -/
theorem source_original_Q_sum_except_one
    {I : Type} [Fintype I] [DecidableEq I]
    (a : I) (f : I → ℝ) :
    (∑ z : {z : I // z ≠ a}, f z.val) + f a =
      ∑ z : I, f z := by
  classical
  have hSubtype :
      (∑ z : {z : I // z ≠ a}, f z.val) =
        ∑ z ∈ (Finset.univ : Finset I).erase a, f z := by
    symm
    apply Finset.sum_subtype (p := fun z : I => z ≠ a)
      ((Finset.univ : Finset I).erase a)
    intro z
    simp
  rw [hSubtype]
  exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)

/- Summing only the first k original Fin n band indices equals
an unrestricted Finset.range k, provided k<=n. -/



/- Exact source owner: SourceOriginalQMacroRestCenterIdentity.lean; original line 11. -/
theorem source_original_Q_macro_rest_midpoint_center
    (r₀ jₓ k : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hk : 0 < k) (hkn : k ≤ jₓ+1) (i : Fin r₀) :
    (∑ z ∈ ((Finset.univ : Finset
        {z : Fin (jₓ+1) × Fin r₀ //
          z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)}).filter
          (fun z => z.val.1.val < k)),
      (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L) =
      L - (11/10:ℝ)*sourceOriginalQ0Scale r₀*L -
        L*(1/2:ℝ)^k := by
  classical
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let t : (Fin (jₓ+1) × Fin r₀) → ℝ := fun z =>
    if z.1.val < k then
      (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.1.val*L
    else 0
  have h0 : t (b,i) =
      (11/10:ℝ)*sourceOriginalQ0Scale r₀*L := by
    simp [t,b,sourceOriginalQActualExponent,hk]
  have hFull : (∑ z : Fin (jₓ+1) × Fin r₀, t z) =
      (∑ j ∈ Finset.range k,
        (r₀:ℝ)*(11/10:ℝ)*sourceOriginalQActualExponent r₀ j*L) := by
    rw [Fintype.sum_prod_type]
    have hBand (j : Fin (jₓ+1)) :
        (∑ m : Fin r₀, t (j,m)) =
        if j.val < k then
          (r₀:ℝ)*(11/10:ℝ)*sourceOriginalQActualExponent r₀ j.val*L
        else 0 := by
      by_cases hj : j.val < k
      · simp [t,hj]
        ring
      · simp [t,hj]
    simp_rw [hBand]
    exact source_original_Q_fin_prefix_sum (jₓ+1) k hkn
      (fun j => (r₀:ℝ)*(11/10:ℝ)*sourceOriginalQActualExponent r₀ j*L)
  have hWithout := source_original_Q_sum_except_one (b,i) t
  have hRight : (∑ z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)},
      t z.val) = L*(1-(1/2:ℝ)^k) -
        (11/10:ℝ)*sourceOriginalQ0Scale r₀*L := by
    rw [hFull, source_original_Q_ideal_fixed_midpoint_sum
      r₀ k L hr₀, h0] at hWithout
    linarith
  have hRest :
      (∑ z ∈ ((Finset.univ : Finset
          {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
          (fun z => z.val.1.val < k)),
          (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L) =
      ∑ z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}, t z.val := by
    rw [Finset.sum_filter]
  change (∑ z ∈ ((Finset.univ : Finset
      {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
      (fun z => z.val.1.val < k)),
      (11/10:ℝ)*sourceOriginalQActualExponent r₀ z.val.1.val*L) = _
  rw [hRest,hRight]
  ring



/- Exact source owner: SourceOriginalQActualMacroRestCorridor.lean; original line 12. -/
theorem source_original_Q_actual_good_macro_rest_corridor
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (hr₀ : 1 ≤ r₀) (hk : 0 < k) (hkn : k ≤ jₓ+1)
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεBudget : ((k*r₀:ℕ):ℝ)*ε ≤ 1/120)
    (i : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
    (hGood : ∀ z, (rest z).val ∈
      sourceOriginalQJointRestAllowed r₀ jₓ k L ε
        ⟨0,Nat.succ_pos jₓ⟩ i z) :
    let qMacro : ℕ := sourceOriginalQRestPartialProduct r₀
      (sourceOriginalQActualBands r₀ jₓ L)
      ⟨0,Nat.succ_pos jₓ⟩ i (fun j => j.val < k) rest
    let center : ℝ := L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L -
      L*(1/2:ℝ)^k
    center - sourceOriginalPDelta r₀ L/24 ≤ Real.log (qMacro:ℝ) ∧
    Real.log (qMacro:ℝ) ≤ center + sourceOriginalPDelta r₀ L/24 := by
  classical
  intro qMacro center
  let A : Finset {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)} :=
    Finset.univ.filter (fun z => z.val.1.val < k)
  have hMid := source_original_Q_macro_rest_midpoint_center
    r₀ jₓ k L hr₀ hk hkn i
  have hDev := source_original_Q_actual_good_macro_product_center
    r₀ jₓ k hr₀ L ε hL hε hεBudget
    ⟨0,Nat.succ_pos jₓ⟩ i rest hGood
  have hEq : qMacro = ∏ z ∈ A, (rest z).val := by
    unfold qMacro sourceOriginalQRestPartialProduct A
    apply Finset.prod_congr
    · ext z
      simp
    · intro z hz
      rfl
  rw [hEq]
  change |Real.log (((∏ z ∈ A, (rest z).val):ℕ):ℝ) -
    (∑ z ∈ A, (11/10:ℝ)*
      sourceOriginalQActualExponent r₀ z.val.1.val*L)| ≤
      sourceOriginalPDelta r₀ L/24 at hDev
  rw [hMid] at hDev
  change |Real.log (((∏ z ∈ A, (rest z).val):ℕ):ℝ) - center| ≤
    sourceOriginalPDelta r₀ L/24 at hDev
  constructor
  · linarith [(abs_sub_le_iff.mp hDev).2]
  · linarith [(abs_sub_le_iff.mp hDev).1]



/- Exact source owner: SourceOriginalQGoodRestMicroBudget.lean; original line 12. -/
noncomputable def sourceOriginalQActualMicroSlotLog
    (r₀ jₓ k : ℕ) (L : ℝ) (hk : 0 < k)
    (i₀ : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
    (j : ℕ) (i : Fin r₀) : ℝ :=
  if hj : j ∈ Finset.Ico k (jₓ+1) then
    let idx : Fin (jₓ+1) := ⟨j,(Finset.mem_Ico.mp hj).2⟩
    let z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)} :=
      ⟨(idx,i),by
        intro heq
        have he := congrArg (fun a : Fin (jₓ+1) × Fin r₀ => a.1.val) heq
        have hjlo := (Finset.mem_Ico.mp hj).1
        change j = 0 at he
        omega⟩
    Real.log ((rest z).val:ℝ)
  else 0

/- Exact source dyadic micro Q-slot logarithm budget at the actual
moving j_x, for every labelled rest tuple. No micro restrictions
or hypothetical endpoint bounds are assumed. -/



/- Exact source owner: SourceOriginalQLogProduct.lean; original line 8. -/
theorem source_original_Q_log_nat_finset_prod
    {I : Type} (s : Finset I) (f : I → ℕ)
    (hpos : ∀ i ∈ s, 0 < f i) :
    Real.log (((∏ i ∈ s, f i):ℕ):ℝ) =
      ∑ i ∈ s, Real.log (f i:ℝ) := by
  have hn : ∀ i ∈ s, (f i:ℝ) ≠ 0 := by
    intro i hi
    exact_mod_cast (Nat.ne_of_gt (hpos i hi))
  simp only [Nat.cast_prod]
  exact Real.log_prod hn



/- Exact source owner: SourceRestMicroReindexCore.lean; original line 10. -/
theorem source_rest_micro_sum_reindex_core
    (r₀ jₓ k : ℕ) (hk : 0 < k) (i₀ : Fin r₀)
    (f : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)} → ℝ)
    (g : ℕ → Fin r₀ → ℝ)
    (hfg : ∀ (j : ℕ) (hj : j ∈ Finset.Ico k (jₓ+1)) (i : Fin r₀),
      g j i =
        f ⟨(⟨j,(Finset.mem_Ico.mp hj).2⟩,i), by
          intro heq
          have hzero := congrArg
            (fun a : Fin (jₓ+1) × Fin r₀ => a.1.val) heq
          have hlo := (Finset.mem_Ico.mp hj).1
          change j = 0 at hzero
          omega⟩) :
    (∑ z ∈ (Finset.univ.filter (fun z :
        {z : Fin (jₓ+1) × Fin r₀ //
          z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)} => ¬ z.val.1.val < k)), f z) =
      ∑ j ∈ Finset.Ico k (jₓ+1), ∑ i : Fin r₀, g j i := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)}
  let S : Finset I := Finset.univ.filter (fun z => ¬ z.val.1.val < k)
  let T : Finset (ℕ × Fin r₀) :=
    (Finset.Ico k (jₓ+1)).product Finset.univ
  change (∑ z ∈ S, f z) = _
  trans ∑ x ∈ T, g x.1 x.2
  · symm
    apply Finset.sum_bij
      (fun x hx =>
        ⟨(⟨x.1, (Finset.mem_Ico.mp
          (Finset.mem_product.mp hx).1).2⟩, x.2), by
            intro heq
            have hzero := congrArg
              (fun a : Fin (jₓ+1) × Fin r₀ => a.1.val) heq
            have hlo := (Finset.mem_Ico.mp
              (Finset.mem_product.mp hx).1).1
            change x.1 = 0 at hzero
            omega⟩)
    · intro x hx
      have hlo := (Finset.mem_Ico.mp (Finset.mem_product.mp hx).1).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mpr hlo⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      apply Prod.ext
      · exact congrArg (fun z : I => z.val.1.val) heq
      · exact congrArg (fun z : I => z.val.2) heq
    · intro z hz
      have hnot : ¬ z.val.1.val < k := (Finset.mem_filter.mp hz).2
      have hlo : k ≤ z.val.1.val := Nat.le_of_not_gt hnot
      let x : ℕ × Fin r₀ := (z.val.1.val,z.val.2)
      have hx : x ∈ T := by
        simp [T, x, Finset.mem_Ico, hlo, z.val.1.isLt]
      refine ⟨x, hx, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> rfl
    · intro x hx
      have hj : x.1 ∈ Finset.Ico k (jₓ+1) :=
        (Finset.mem_product.mp hx).1
      simpa only using (hfg x.1 hj x.2)
  · dsimp [T]
    exact Finset.sum_product (Finset.Ico k (jₓ+1))
      (Finset.univ : Finset (Fin r₀)) (fun x => g x.1 x.2)



/- Exact source owner: SourceOriginalQPActualGoodRestCorridor.lean; original line 14. -/
theorem source_original_Q_actual_micro_partial_log_exact
    (r₀ jₓ k : ℕ) (L : ℝ) (hk : 0 < k) (hkn : k ≤ jₓ+1)
    (i₀ : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1}) :
    Real.log ((sourceOriginalQRestPartialProduct r₀
      (sourceOriginalQActualBands r₀ jₓ L)
      ⟨0,Nat.succ_pos jₓ⟩ i₀ (fun j => ¬ j.val < k) rest : ℕ) : ℝ) =
      ∑ j ∈ Finset.Ico k (jₓ+1), ∑ i : Fin r₀,
        sourceOriginalQActualMicroSlotLog r₀ jₓ k L hk i₀ rest j i := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)}
  let S : Finset I := Finset.univ.filter (fun z => ¬ z.val.1.val < k)
  have hpos : ∀ z ∈ S, 0 < (rest z).val := by
    intro z hz
    exact (source_original_Q_actual_prime r₀ jₓ L z.val.1
      (rest z).val (rest z).property).pos
  have hProductEq :
      sourceOriginalQRestPartialProduct r₀
          (sourceOriginalQActualBands r₀ jₓ L)
          ⟨0,Nat.succ_pos jₓ⟩ i₀ (fun j => ¬ j.val < k) rest =
        ∏ z ∈ S, (rest z).val := by
    unfold sourceOriginalQRestPartialProduct
    apply Finset.prod_congr
    · ext z
      simp [S, I]
    · intro z hz
      rfl
  rw [hProductEq]
  rw [source_original_Q_log_nat_finset_prod S (fun z => (rest z).val) hpos]
  apply source_rest_micro_sum_reindex_core r₀ jₓ k hk i₀
    (fun z => Real.log ((rest z).val : ℝ))
    (sourceOriginalQActualMicroSlotLog r₀ jₓ k L hk i₀ rest)
  intro j hj i
  simp [sourceOriginalQActualMicroSlotLog, hj]


/- The same explicit power condition used for the micro tail also
controls the ideal missing midpoint tail. -/



/- Exact source owner: SourceOriginalQMicroDyadicTail.lean; original line 7. -/
theorem source_original_Q_dyadic_sum_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (1/2:ℝ)^j) =
      2*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/- The TOTAL size of all dyadic micro Q bands above a fixed index k
is bounded by twice their first scale, uniformly in moving j_x. -/



/- Exact source owner: SourceOriginalQMicroDyadicTail.lean; original line 18. -/
theorem source_original_Q_dyadic_tail_upper
    (k n : ℕ) (hkn : k ≤ n) :
    (∑ j ∈ Finset.Ico k n, (1/2:ℝ)^j) ≤
      2*(1/2:ℝ)^k := by
  rw [Finset.sum_Ico_eq_sub _ hkn,
    source_original_Q_dyadic_sum_range n,
    source_original_Q_dyadic_sum_range k]
  have hPow : (0:ℝ) ≤ (1/2:ℝ)^n := by positivity
  linarith

/- An explicit fixed index k with 2^k >= 288*r₀ controls the
ORIGINAL micro log-budget. This estimate is independent of j_x. -/



/- Exact source owner: SourceOriginalQMicroDyadicTail.lean; original line 30. -/
theorem source_original_Q_micro_scalar_budget
    (r₀ k n : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : 0 ≤ L) (hkn : k ≤ n)
    (hk : 288*r₀ ≤ 2^k) :
    (r₀:ℝ) * (6/5:ℝ) *
        (5/(11*(r₀:ℝ))) * L *
        (∑ j ∈ Finset.Ico k n, (1/2:ℝ)^j) ≤
      L/(264*(r₀:ℝ)) := by
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  have hkR : (288:ℝ)*(r₀:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast hk
  have hTail := source_original_Q_dyadic_tail_upper k n hkn
  have hFactor : 0 ≤ (r₀:ℝ)*(6/5:ℝ)*(5/(11*(r₀:ℝ)))*L := by
    positivity
  have hBound := mul_le_mul_of_nonneg_left hTail hFactor
  have hPInv : (1/2:ℝ)^k = ((2:ℝ)^k)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rw [hPInv] at hBound
  have h288 : (0:ℝ) < 288*(r₀:ℝ) := by positivity
  have hInv : ((2:ℝ)^k)⁻¹ ≤ (288*(r₀:ℝ))⁻¹ :=
    (inv_le_inv₀ hp h288).mpr hkR
  have hInvBound := mul_le_mul_of_nonneg_left hInv (by positivity :
      2*((r₀:ℝ)*(6/5:ℝ)*(5/(11*(r₀:ℝ)))*L) ≥ 0)
  have hr0 : (r₀:ℝ) ≠ 0 := ne_of_gt hr
  calc
    _ ≤ ((r₀:ℝ)*(6/5:ℝ)*(5/(11*(r₀:ℝ)))*L) *
        (2*((2:ℝ)^k)⁻¹) := hBound
    _ ≤ ((r₀:ℝ)*(6/5:ℝ)*(5/(11*(r₀:ℝ)))*L) *
        (2*((288*(r₀:ℝ))⁻¹)) := by
          gcongr
    _ = _ := by
      field_simp
      ring



/- Exact source owner: SourceOriginalQMicroLogBudget.lean; original line 11. -/
theorem source_original_Q_micro_slot_log_budget
    (r₀ k n : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : 0 ≤ L) (hkn : k ≤ n) (hk : 288*r₀ ≤ 2^k)
    (slotLog : ℕ → Fin r₀ → ℝ)
    (hBound : ∀ j ∈ Finset.Ico k n, ∀ i : Fin r₀,
      slotLog j i ≤ (6/5:ℝ)*(5/(11*(r₀:ℝ)))*L*(1/2:ℝ)^j) :
    (∑ j ∈ Finset.Ico k n,
      ∑ i : Fin r₀, slotLog j i) ≤ L/(264*(r₀:ℝ)) := by
  have hPerBand (j : ℕ) (hj : j ∈ Finset.Ico k n) :
      (∑ i : Fin r₀, slotLog j i) ≤
        (r₀:ℝ)*((6/5:ℝ)*(5/(11*(r₀:ℝ)))*L*(1/2:ℝ)^j) := by
    calc
      (∑ i : Fin r₀, slotLog j i) ≤
        ∑ _i : Fin r₀,
          (6/5:ℝ)*(5/(11*(r₀:ℝ)))*L*(1/2:ℝ)^j := by
            apply Finset.sum_le_sum
            intro i hi
            exact hBound j hj i
      _ = _ := by simp [mul_comm]
  have hSum : (∑ j ∈ Finset.Ico k n,
      ∑ i : Fin r₀, slotLog j i) ≤
      ((r₀:ℝ)*(6/5:ℝ)*(5/(11*(r₀:ℝ)))*L) *
        (∑ j ∈ Finset.Ico k n, (1/2:ℝ)^j) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico k n,
        (r₀:ℝ)*((6/5:ℝ)*(5/(11*(r₀:ℝ)))*L*(1/2:ℝ)^j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hPerBand j hj
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  exact hSum.trans
    (source_original_Q_micro_scalar_budget r₀ k n L hr₀ hL hkn hk)



/- Exact source owner: SourceOriginalQGoodRestMicroBudget.lean; original line 35. -/
theorem source_original_Q_actual_micro_rest_log_budget
    (r₀ jₓ k : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hk : 0 < k) (hL : 0 ≤ L)
    (hkn : k ≤ jₓ+1) (hkPower : 288*r₀ ≤ 2^k)
    (i₀ : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1}) :
    (∑ j ∈ Finset.Ico k (jₓ+1), ∑ i : Fin r₀,
      sourceOriginalQActualMicroSlotLog r₀ jₓ k L hk i₀ rest j i) ≤
      sourceOriginalPDelta r₀ L / 24 := by
  let slotLog : ℕ → Fin r₀ → ℝ :=
    sourceOriginalQActualMicroSlotLog r₀ jₓ k L hk i₀ rest
  have hs (j : ℕ) :
      sourceOriginalQActualExponent r₀ j =
      (5/(11*(r₀:ℝ)))*(1/2:ℝ)^j := by
    unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  have hBound : ∀ j ∈ Finset.Ico k (jₓ+1), ∀ i : Fin r₀,
    slotLog j i ≤ (6/5:ℝ)*(5/(11*(r₀:ℝ)))*L*(1/2:ℝ)^j := by
    intro j hj i
    let idx : Fin (jₓ+1) := ⟨j,(Finset.mem_Ico.mp hj).2⟩
    let z : {z : Fin (jₓ+1) × Fin r₀ //
        z ≠ (⟨0,Nat.succ_pos jₓ⟩,i₀)} :=
      ⟨(idx,i),by
        intro heq
        have he := congrArg (fun a : Fin (jₓ+1) × Fin r₀ => a.1.val) heq
        have hjlo := (Finset.mem_Ico.mp hj).1
        change j = 0 at he
        omega⟩
    have hLog : slotLog j i = Real.log ((rest z).val:ℝ) := by
      simp [slotLog,sourceOriginalQActualMicroSlotLog,hj,idx,z]
    have hp : (rest z).val ∈ sourceClosedPrimeLogBand L
        (sourceOriginalQActualExponent r₀ j)
        ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j) :=
      (rest z).property
    have hUp := (source_original_Q_closed_prime_log_bounds L
      (sourceOriginalQActualExponent r₀ j)
      ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j)
      (rest z).val hp).2
    calc
      slotLog j i = Real.log ((rest z).val:ℝ) := hLog
      _ ≤ (6/5:ℝ)*sourceOriginalQActualExponent r₀ j*L := hUp
      _ = _ := by rw [hs]; ring
  have hBudget := source_original_Q_micro_slot_log_budget
    r₀ k (jₓ+1) L hr₀ hL hkn hkPower slotLog hBound
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  change (∑ j ∈ Finset.Ico k (jₓ+1), ∑ i : Fin r₀,
      slotLog j i) ≤ sourceOriginalPDelta r₀ L/24
  calc
    _ ≤ L/(264*(r₀:ℝ)) := hBudget
    _ = sourceOriginalPDelta r₀ L/24 := by
      unfold sourceOriginalPDelta
      field_simp
      ring



/- Exact source owner: SourceOriginalQPActualGoodRestCorridor.lean; original line 55. -/
theorem source_original_Q_ideal_tail_budget_of_power
    (r₀ k : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 ≤ L)
    (hkPower : 288*r₀ ≤ 2^k) :
    L*(1/2:ℝ)^k ≤ sourceOriginalPDelta r₀ L/24 := by
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  have hkR : (288:ℝ)*(r₀:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast hkPower
  have h264 : (264:ℝ)*(r₀:ℝ) ≤ (2:ℝ)^k := by
    have hh : 0 ≤ (24:ℝ)*(r₀:ℝ) := by positivity
    nlinarith
  have hInv : ((2:ℝ)^k)⁻¹ ≤ ((264:ℝ)*(r₀:ℝ))⁻¹ :=
    (inv_le_inv₀ hp (by positivity)).mpr h264
  have hpow : (1/2:ℝ)^k = ((2:ℝ)^k)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rw [hpow]
  calc
    L*((2:ℝ)^k)⁻¹ ≤ L*((264:ℝ)*(r₀:ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hInv hL
    _ = sourceOriginalPDelta r₀ L/24 := by
      unfold sourceOriginalPDelta
      field_simp
      ring

/- Full deterministic corridor for the actual good Q-rest multiplied by
an actual positive P-supported integer obeying the certified small-log
condition.  This is the geometry needed by the free-Q0 Psi count. -/



/- Exact source owner: SourceOriginalQRestProductSplit.lean; original line 39. -/
theorem source_original_Q_rest_partial_product_pos
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (keep : B → Prop)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1})
    (hPrime : ∀ j p, p ∈ Q j → p.Prime) :
    0 < sourceOriginalQRestPartialProduct r Q b i keep rest := by
  classical
  unfold sourceOriginalQRestPartialProduct
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact (hPrime k.val.1 (rest k).val (rest k).property).ne_zero

/- Exact logarithmic macro+micro decomposition for the true rest
Q integer product, independently of the original cutoff Ψ. -/



/- Exact source owner: SourceOriginalQRestProductSplit.lean; original line 22. -/
theorem source_original_Q_rest_partial_product_split
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (keep : B → Prop)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1}) :
    sourceOriginalQRestPartialProduct r Q b i keep rest *
    sourceOriginalQRestPartialProduct r Q b i (fun j => ¬keep j) rest =
      ∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val := by
  classical
  let I := {k : B × Fin r // k ≠ (b,i)}
  simpa [sourceOriginalQRestPartialProduct] using
    (Finset.prod_filter_mul_prod_filter_not
      (Finset.univ : Finset I)
      (fun k : I => keep k.val.1) (fun k => (rest k).val))

/- Every partial product of genuine source Q prime slots is positive. -/



/- Exact source owner: SourceOriginalGoodRestCombination.lean; original line 25. -/
theorem source_original_good_rest_log_budget
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (qFixed qMicro R : ℕ) (hFixedPos : 0 < qFixed)
    (hMicroPos : 0 < qMicro) (hRPos : 0 < R)
    (bTail : ℝ)
    (hTailNonneg : 0 ≤ bTail)
    (hTailBound : bTail ≤ sourceOriginalPDelta r₀ L/24)
    (hFixedLo : L - (11/10:ℝ)*sourceOriginalQ0Scale r₀*L -
        bTail - sourceOriginalPDelta r₀ L/24 ≤ Real.log (qFixed:ℝ))
    (hFixedHi : Real.log (qFixed:ℝ) ≤
        L - (11/10:ℝ)*sourceOriginalQ0Scale r₀*L -
        bTail + sourceOriginalPDelta r₀ L/24)
    (hMicroLo : 0 ≤ Real.log (qMicro:ℝ))
    (hMicroHi : Real.log (qMicro:ℝ) ≤ sourceOriginalPDelta r₀ L/24)
    (hRLo : 0 ≤ Real.log (R:ℝ))
    (hRHi : Real.log (R:ℝ) ≤ sourceOriginalPDelta r₀ L/12) :
    L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
      sourceOriginalQ0Scale r₀*L/30 ≤
      Real.log ((qFixed*qMicro*R : ℕ) : ℝ) ∧
    Real.log ((qFixed*qMicro*R : ℕ) : ℝ) ≤
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
        sourceOriginalQ0Scale r₀*L/30 := by
  have hf : (qFixed:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hFixedPos)
  have hm : (qMicro:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hMicroPos)
  have hp : (R:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hRPos)
  have hfm : (qFixed:ℝ)*(qMicro:ℝ) ≠ 0 := mul_ne_zero hf hm
  have hLog : Real.log ((qFixed*qMicro*R : ℕ) : ℝ) =
      Real.log (qFixed:ℝ) + Real.log (qMicro:ℝ) +
        Real.log (R:ℝ) := by
    push_cast
    rw [Real.log_mul hfm hp, Real.log_mul hf hm]
  have hDelta := source_original_P_delta_eq_Q0_width r₀ L hr₀
  rw [hLog]
  constructor
  · rw [hDelta] at hTailBound hFixedLo hFixedHi hMicroHi hRHi
    linarith
  · rw [hDelta] at hTailBound hFixedLo hFixedHi hMicroHi hRHi
    linarith


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Mass009 -/

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
open Filter Topology Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceOriginalQPActualGoodRestCorridor.lean; original line 84. -/
theorem source_original_QP_actual_good_rest_corridor
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (hr₀ : 1 ≤ r₀) (hk : 0 < k) (hkn : k ≤ jₓ+1)
    (hkPower : 288*r₀ ≤ 2^k)
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hεBudget : ((k*r₀:ℕ):ℝ)*ε ≤ 1/120)
    (i : Fin r₀)
    (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
      z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)}) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
    (hGood : ∀ z, (rest z).val ∈
      sourceOriginalQJointRestAllowed r₀ jₓ k L ε
        ⟨0,Nat.succ_pos jₓ⟩ i z)
    (R : ℕ) (hRPos : 0 < R)
    (hRHi : Real.log (R:ℝ) ≤ sourceOriginalPDelta r₀ L/12) :
    let qRest : ℕ := ∏ z, (rest z).val
    L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤
      Real.log ((qRest*R:ℕ):ℝ) ∧
    Real.log ((qRest*R:ℕ):ℝ) ≤
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
        sourceOriginalQ0Scale r₀*L/30 := by
  classical
  intro qRest
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let qMacro : ℕ := sourceOriginalQRestPartialProduct r₀ Q b i
    (fun j => j.val < k) rest
  let qMicro : ℕ := sourceOriginalQRestPartialProduct r₀ Q b i
    (fun j => ¬ j.val < k) rest
  have hMacro := source_original_Q_actual_good_macro_rest_corridor
    r₀ jₓ k L ε hr₀ hk hkn hL hε hεBudget i rest hGood
  have hMicroSum := source_original_Q_actual_micro_rest_log_budget
    r₀ jₓ k L hr₀ hk hL hkn hkPower i rest
  have hMicroEq := source_original_Q_actual_micro_partial_log_exact
    r₀ jₓ k L hk hkn i rest
  have hMicroHi : Real.log (qMicro:ℝ) ≤
      sourceOriginalPDelta r₀ L/24 := by
    change Real.log ((sourceOriginalQRestPartialProduct r₀
      (sourceOriginalQActualBands r₀ jₓ L)
      ⟨0,Nat.succ_pos jₓ⟩ i (fun j => ¬ j.val < k) rest : ℕ) : ℝ) ≤
        sourceOriginalPDelta r₀ L/24
    rw [hMicroEq]
    exact hMicroSum
  have hMacroPos : 0 < qMacro :=
    source_original_Q_rest_partial_product_pos r₀ Q b i
      (fun j => j.val < k) rest
      (source_original_Q_actual_prime r₀ jₓ L)
  have hMicroPos : 0 < qMicro :=
    source_original_Q_rest_partial_product_pos r₀ Q b i
      (fun j => ¬ j.val < k) rest
      (source_original_Q_actual_prime r₀ jₓ L)
  have hMicroLo : 0 ≤ Real.log (qMicro:ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hMicroPos)
  have hRLo : 0 ≤ Real.log (R:ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hRPos)
  have hTail := source_original_Q_ideal_tail_budget_of_power
    r₀ k L hr₀ hL hkPower
  have hSplit := source_original_Q_rest_partial_product_split
    r₀ Q b i (fun j => j.val < k) rest
  have hqRest : qRest = qMacro*qMicro := by
    dsimp [qRest, qMacro, qMicro, Q, b]
    exact hSplit.symm
  rw [hqRest]
  apply source_original_good_rest_log_budget r₀ L hr₀
    qMacro qMicro R hMacroPos hMicroPos hRPos
    (L*(1/2:ℝ)^k)
  · positivity
  · exact hTail
  · exact hMacro.1
  · exact hMacro.2
  · exact hMicroLo
  · exact hMicroHi
  · exact hRLo
  · exact hRHi



/- Exact source owner: SourceOriginalXAPointwiseNative.lean; original line 24. -/
theorem source_original_XA_actual_good_pointwise_floor_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ)
    (hε : 0 ≤ ε)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀)
      (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
        z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)}) →
        {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
      (R : sourceOriginalPSupported
        (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L))),
      (∀ z, (rest z).val ∈
        sourceOriginalQJointRestAllowed r₀ jₓ k L ε
          ⟨0,Nat.succ_pos jₓ⟩ i z) →
      Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 →
      let q : ℕ := ∏ z, (rest z).val
      let a : ℝ :=
        (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) / (q:ℝ)
      let w : ℝ :=
        (sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) R.val /
          (R.val:ℝ)) *
        ((1-(-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) R.val)/2)
      sourceOriginalXAGoodPrefactor r₀ L α β c * (a*w) ≤
        sourceOriginalQPActualFreeTerm r₀
          (sourceOriginalQActualBands r₀ jₓ L)
          (sourceOriginalPAllActualBands r₀ L)
          ⟨0,Nat.succ_pos jₓ⟩ i (Real.exp L) Ψ rest R := by
  have hFree := source_original_Q0_actual_XA_free_prime_floor_eventually
    r₀ hr₀ α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hFree, eventually_gt_atTop (0:ℝ)] with L hFreeL hL
  intro jₓ hkn i rest R hGood hRHi q a w
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  have hCorr := source_original_QP_actual_good_rest_corridor
    r₀ jₓ k L ε hr₀ hk hkn hkPower hL.le hε hεBudget
      i rest hGood R.val (Nat.pos_of_ne_zero R.property.1) hRHi
  have hFloor := hFreeL Q P b i
    (source_original_Q_actual_prime r₀ jₓ L)
    (by simp [Q, b, sourceOriginalQActualBands, sourceOriginalQActualExponent]) rest R hCorr.1 hCorr.2
  have hq : 0 < q := by
    dsimp [q]
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    exact (source_original_Q_actual_prime r₀ jₓ L z.val.1
      (rest z).val (rest z).property).ne_zero
  have hR : 0 < R.val := Nat.pos_of_ne_zero R.property.1
  have hRewrite :
      sourceOriginalXAGoodPrefactor r₀ L α β c * (a*w) =
      ((∏ _j : Fin (jₓ+1), (1:ℝ)/(r₀.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1-(-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)) *
      ((α*Real.exp L/(q*R.val:ℕ)) *
        (c*Real.log (β/α) /
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L))) := by
    dsimp only [sourceOriginalXAGoodPrefactor, a, w, P]
    simp only [Nat.cast_mul, one_div, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hRewrite]
  change _ ≤ sourceOriginalQPActualFreeTerm r₀ Q P b i (Real.exp L) Ψ rest R
  simpa only [sourceOriginalQPActualFreeTerm, Q, P, b] using hFloor



/- Exact source owner: SourceOriginalXAGoodHarmonicLower.lean; original line 10. -/
theorem source_original_XA_actual_good_harmonic_floor_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ)
    (hε : 0 ≤ ε)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀),
      sourceOriginalXAGoodPrefactor r₀ L α β c *
        sourceOriginalQPActualGoodHarmonicMass
          r₀ jₓ k L ε ⟨0,Nat.succ_pos jₓ⟩ i ≤
      sourceOriginalXA r₀
        (sourceOriginalQActualBands r₀ jₓ L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  have hPoint := source_original_XA_actual_good_pointwise_floor_eventually
    r₀ k hr₀ hk hkPower ε α β c Ψ hε hεBudget
      hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hPoint, eventually_gt_atTop (0:ℝ)] with L hPointL hL
  intro jₓ hkn i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
  let E (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ Q z.val.1})
      (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : Prop :=
    (∀ z, (rest z).val ∈ Good z) ∧
      Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
  let a (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ Q z.val.1}) : ℝ :=
    (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
      ((((∏ z, (rest z).val):ℕ):ℝ))
  let w (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
    (sourceOriginalW1 P R.val/(R.val:ℝ)) *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2)
  let K := sourceOriginalXAGoodPrefactor r₀ L α β c
  have hPrune := source_original_XA_QP_good_rest_lower
    r₀ Q P b i (Real.exp L) Ψ hΨnonneg
    (source_original_Q_actual_prime r₀ jₓ L)
    (source_original_Q_actual_all_disjoint r₀ jₓ L hr₀ hL)
    (source_original_P_all_actual_band_prime r₀ L)
    (source_original_Q_actual_all_P_disjoint r₀ jₓ L hr₀ hL)
    E
  have hTerm : ∀ rest R, (if E rest R then K*(a rest*w R) else 0) ≤
      (if E rest R then
        sourceOriginalQPActualFreeTerm r₀ Q P b i (Real.exp L) Ψ rest R
       else 0) := by
    intro rest R
    by_cases hE : E rest R
    · rw [if_pos hE, if_pos hE]
      dsimp only [K, a, w, Q, P, b]
      exact hPointL jₓ hkn i rest R hE.1 hE.2
    · simp [hE]
  apply le_trans ?_ hPrune
  unfold sourceOriginalQPActualGoodHarmonicMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rest hrest
  rw [← tsum_mul_left]
  simp only [mul_ite, mul_zero]
  have hLhs : (∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (∀ z, (rest z).val ∈ Good z) ∧
          Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
        sourceOriginalXAGoodPrefactor r₀ L α β c *
          (((∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z, (rest z).val):ℕ):ℝ)) *
            ((sourceOriginalW1 P R.val/(R.val:ℝ)) *
              ((1-(-1:ℝ)^sourceOriginalPParityExponent
                (Finset.univ.biUnion P) R.val)/2))) else 0) =
      ∑' R, if E rest R then K*(a rest*w R) else 0 := by
    apply tsum_congr
    intro R
    simp only [E, K, a, w]
    split_ifs <;> rfl
  rw [hLhs]
  have hUpper : Summable (fun R =>
      if E rest R then
        sourceOriginalQPActualFreeTerm r₀ Q P b i (Real.exp L) Ψ rest R
      else 0) := by
    have hFull := source_original_QP_actual_free_term_summable
      r₀ Q P b i (Real.exp L) Ψ
        (source_original_Q_actual_prime r₀ jₓ L) rest
    have hn (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :=
      source_original_QP_actual_free_term_nonneg
        r₀ Q P b i (Real.exp L) Ψ hΨnonneg rest R
    exact hFull.of_nonneg_of_le
      (fun R => by split_ifs <;> [exact hn R; exact le_rfl])
      (fun R => by split_ifs <;> [exact le_rfl; exact hn R])
  have hLowerNonneg : ∀ R,
      0 ≤ (if E rest R then K*(a rest*w R) else 0) := by
    intro R
    by_cases hE : E rest R
    · rw [if_pos hE]
      have hlog : 0 < Real.log (β/α) := Real.log_pos
        ((one_lt_div (by linarith : 0 < α)).2 hαβ)
      have hs : 0 < sourceOriginalQ0Scale r₀ := by
        unfold sourceOriginalQ0Scale
        have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
        positivity
      have hd : 0 < (6/5:ℝ)*sourceOriginalQ0Scale r₀-sourceOriginalQ0Scale r₀/30 := by linarith
      have hK : 0 ≤ K := by dsimp [K, sourceOriginalXAGoodPrefactor]; positivity
      have ha : 0 ≤ a rest := by dsimp [a]; positivity
      have hp : 0 ≤ (1-(-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2 := by
        rcases source_original_parity_projection_zero_or_one
          (Finset.univ.biUnion P) R.val with h | h <;> rw [h] <;> norm_num
      have hw : 0 ≤ w R := by
        exact mul_nonneg (div_nonneg (source_original_W1_nonneg P R.val)
          (by positivity)) hp
      exact mul_nonneg hK (mul_nonneg ha hw)
    · simp [hE]
  have hLower := hUpper.of_nonneg_of_le hLowerNonneg (hTerm rest)
  have hSum := Summable.tsum_le_tsum (hTerm rest) hLower hUpper
  convert hSum using 1
  apply tsum_congr
  intro R
  split_ifs <;> rfl



/- Exact source owner: SourceShiftTwoXAHarmonicQ.lean; original line 9. -/
theorem source_original_labelled_Q_harmonic_mass
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) :
    (∑ f : (i : B × Fin r) → {p // p ∈ Q i.1},
      (∏ _b : B, (r.factorial:ℝ)⁻¹) /
        ((∏ i : B × Fin r, (f i).val : ℕ) : ℝ)) =
      ∏ b : B, ((∑ p ∈ Q b, (p:ℝ)⁻¹)^r/(r.factorial:ℝ)) := by
  classical
  have h := Green64FiniteExtraction.assignment_reciprocal
    (fun i : B × Fin r => Q i.1)
    (∏ _b : B, (r.factorial:ℝ)⁻¹)
  rw [h]
  have hs :
      (∏ i : B × Fin r, ∑ p ∈ Q i.1, (p:ℝ)⁻¹) =
        ∏ b : B, (∑ p ∈ Q b, (p:ℝ)⁻¹)^r := by
    rw [Fintype.prod_prod_type]
    simp
  rw [hs, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b hb
  ring

/- Same exact sampling identity in the literal macro+micro H_Q. -/



/- Exact source owner: SourceOriginalXAFinalHarmonicLower.lean; original line 17. -/
theorem source_original_XA_actual_HQ_HP_floor_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/10)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 < c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀),
      let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
      let δ := sourceOriginalPGroupParityDelta/2
      let HQ := sourceOriginalQActualHQ r₀ jₓ L
      let HP := sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)
      (sourceOriginalXAGoodPrefactor r₀ L α β c*γ*δ/16)*(HQ*HP) ≤
        sourceOriginalXA r₀
          (sourceOriginalQActualBands r₀ jₓ L)
          (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  have hXA := source_original_XA_actual_good_harmonic_floor_eventually
    r₀ k hr₀ hk hkPower ε α β c Ψ hε.le hεBudget
      hα hαβ hβ hc.le hΨnonneg hΨ
  have hMass := source_original_QP_actual_good_mass_product_floor_eventually
    r₀ k hr₀ ε hε hεsmall
  have hLocal := source_original_P_all_actual_local_eventually r₀
  filter_upwards [hXA, hMass, hLocal, eventually_gt_atTop (0:ℝ)]
    with L hXAL hMassL hLocalL hL
  intro jₓ hkn i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let G := sourceOriginalQPActualGoodHarmonicMass r₀ jₓ k L ε b i
  let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ := sourceOriginalPGroupParityDelta/2
  let HQ := sourceOriginalQActualHQ r₀ jₓ L
  let HP := sourceLiteralHP P
  let K := sourceOriginalXAGoodPrefactor r₀ L α β c
  let XA := sourceOriginalXA r₀ Q P (Real.exp L) Ψ
  have hGoodRaw := hMassL jₓ i
  have hGood : (γ*δ)*(HQ*HP) ≤ 4*G := by
    dsimp only [G]
    rw [source_original_QP_actual_good_harmonic_product]
    rw [source_original_labelled_Q_harmonic_mass r₀
      (sourceOriginalQActualBands r₀ jₓ L)] at hGoodRaw
    simpa only [γ, δ, HQ, HP, G, Q, P, b,
      sourceOriginalQActualHQ, sourceOriginalPActualGoodHarmonicMass,
      mul_assoc] using hGoodRaw
  have hFloor : K*G ≤ XA := by
    dsimp [K, G, XA, Q, P, b]
    exact hXAL jₓ hkn i
  have hγ : 0 ≤ γ := by
    dsimp [γ]
    exact (pow_pos (source_original_Q_uniform_gamma_positive_le_one
      ε hε hεsmall).1 _).le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact (div_pos source_original_P_group_parity_delta_positive
      (by norm_num)).le
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocalL.2.1 g p hp)
  have hHP : 0 ≤ HP := by
    dsimp [HP]
    exact (source_literal_HP_one_le P h3 hLocalL.1).trans' (by norm_num)
  have hK : 0 ≤ K := by
    dsimp [K, sourceOriginalXAGoodPrefactor]
    have hs : 0 < sourceOriginalQ0Scale r₀ := by
      unfold sourceOriginalQ0Scale
      positivity
    have hd : 0 < (6/5:ℝ)*sourceOriginalQ0Scale r₀-
        sourceOriginalQ0Scale r₀/30 :=
      source_original_Q0_denominator_pos _ hs
    have hlog : 0 < Real.log (β/α) := Real.log_pos
      ((one_lt_div (by linarith : 0 < α)).2 hαβ)
    positivity
  have hNonneg : 0 ≤ (γ*δ)*(HQ*HP) := by
    have hHQ : 0 ≤ HQ := by
      dsimp [HQ, sourceOriginalQActualHQ]
      positivity
    positivity
  have hWeak : (γ*δ)*(HQ*HP)/16 ≤ G := by
    have hG : 0 ≤ G := by nlinarith [hGood]
    nlinarith [hGood]
  calc
    (K*γ*δ/16)*(HQ*HP) = K*((γ*δ)*(HQ*HP)/16) := by ring
    _ ≤ K*G := mul_le_mul_of_nonneg_left hWeak hK
    _ ≤ XA := hFloor



/- Exact source owner: SourceOriginalXAMassCompositionCore.lean; original line 36. -/
theorem source_original_XA_prefactor_extract
    (α c logRatio γ δ d x L HQ HP : ℝ)
    (hd : d ≠ 0) (hL : L ≠ 0) :
    ((α*x*(c*logRatio/(4*d*L)))*γ*δ/16)*(HQ*HP) =
      sourceOriginalXAMassConstant α c logRatio γ δ d *
        (x/L)*(HQ*HP) := by
  unfold sourceOriginalXAMassConstant
  field_simp
  ring



/- Exact source owner: SourceOriginalMovingDepthCore.lean; original line 36. -/
theorem source_original_fixed_depth_le_of_largest
    (r₀ k jₓ : ℕ) (L : ℝ)
    (hk : sourceOriginalDepthAdmissible r₀ k L)
    (hLargest : ∀ j, sourceOriginalDepthAdmissible r₀ j L → j ≤ jₓ) :
    k ≤ jₓ + 1 := by
  exact (hLargest k hk).trans (Nat.le_succ jₓ)

/- Eventual fixed-depth inclusion, isolated with precisely the
manuscript obligation that the chosen `jₓ(L)` is largest admissible. -/



/- Exact source owner: SourceOriginalMovingDepthCore.lean; original line 45. -/
theorem source_original_fixed_depth_below_moving_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (jₓ : ℝ → ℕ)
    (hLargest : ∀ᶠ L : ℝ in atTop,
      ∀ j, sourceOriginalDepthAdmissible r₀ j L → j ≤ jₓ L) :
    ∀ᶠ L : ℝ in atTop, k ≤ jₓ L + 1 := by
  filter_upwards [source_original_fixed_depth_admissible_eventually r₀ k hr₀,
    hLargest] with L hk hmax
  exact source_original_fixed_depth_le_of_largest r₀ k (jₓ L) L hk hmax



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 7. -/
theorem source_original_fixed_macro_count_pos
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) : 0 < 400*r₀ := by
  omega

/- The fixed source macro count supplies the stronger natural-number
power budget required by the actual good-rest corridor. -/



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 13. -/
theorem source_original_fixed_macro_count_power
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) : 288*r₀ ≤ 2^(400*r₀) := by
  have hle : 288*r₀ ≤ 400*r₀ := by omega
  have hlt : 400*r₀ < 2^(400*r₀) := (400*r₀).lt_two_pow_self
  omega

/- An explicit positive relative midpoint width satisfying both the
`ε ≤ 1/10` mass hypothesis and the corridor budget
`(k*r₀)ε ≤ 1/120` when `k=400*r₀`. -/



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 41. -/
theorem source_original_fixed_macro_epsilon_budget
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ((((400*r₀)*r₀:ℕ):ℝ) * sourceOriginalFixedMacroEpsilon r₀) ≤ 1/120 := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
  unfold sourceOriginalFixedMacroEpsilon
  push_cast
  field_simp
  norm_num

/- The literal Q₀ lower logarithmic endpoint eventually lies above two,
which is exactly the size premise of the checked HQ-to-rest comparison. -/



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 32. -/
theorem source_original_fixed_macro_epsilon_le_tenth
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    sourceOriginalFixedMacroEpsilon r₀ ≤ (1/10:ℝ) := by
  have hr : (1:ℝ) ≤ r₀ := by exact_mod_cast hr₀
  unfold sourceOriginalFixedMacroEpsilon
  have hp : (0:ℝ) < 48000*(r₀:ℝ)^2 := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith [sq_nonneg ((r₀:ℝ)-1)]



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 25. -/
theorem source_original_fixed_macro_epsilon_pos
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    0 < sourceOriginalFixedMacroEpsilon r₀ := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
  unfold sourceOriginalFixedMacroEpsilon
  positivity



/- Exact source owner: SourceOriginalXAFixedParameterLower.lean; original line 49. -/
theorem source_original_XA_fixed_parameter_lower_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t)
    (jₓ : ℝ → ℕ)
    (hLargest : ∀ᶠ L : ℝ in atTop,
      ∀ j, sourceOriginalDepthAdmissible r₀ j L → j ≤ jₓ L) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant r₀ α β c *
        (Real.exp L/L) *
        (sourceOriginalQActualHQ r₀ (jₓ L) L *
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      sourceOriginalXA r₀
        (sourceOriginalQActualBands r₀ (jₓ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  let k := 400*r₀
  let ε := sourceOriginalFixedMacroEpsilon r₀
  have hk : 0 < k := by
    dsimp [k]
    exact source_original_fixed_macro_count_pos r₀ hr₀
  have hkPower : 288*r₀ ≤ 2^k := by
    dsimp [k]
    exact source_original_fixed_macro_count_power r₀ hr₀
  have hε : 0 < ε := by
    dsimp [ε]
    exact source_original_fixed_macro_epsilon_pos r₀ hr₀
  have hεsmall : ε ≤ 1/10 := by
    dsimp [ε]
    exact source_original_fixed_macro_epsilon_le_tenth r₀ hr₀
  have hεBudget : ((((k*r₀:ℕ):ℝ))*ε) ≤ 1/120 := by
    dsimp [k, ε]
    exact source_original_fixed_macro_epsilon_budget r₀ hr₀
  have hBase := source_original_XA_actual_HQ_HP_floor_eventually
    r₀ k hr₀ hk hkPower ε α β c Ψ hε hεsmall hεBudget
      hα hαβ hβ hc hΨnonneg hΨ
  have hDepth := source_original_fixed_depth_below_moving_eventually
    r₀ k hr₀ jₓ hLargest
  filter_upwards [hBase, hDepth, eventually_gt_atTop (0:ℝ)]
    with L hBaseL hkn hL
  have hh := hBaseL (jₓ L) hkn ⟨0,lt_of_lt_of_le (by omega : 0 < 1) hr₀⟩
  let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ := sourceOriginalPGroupParityDelta/2
  let d := (6/5:ℝ)*sourceOriginalQ0Scale r₀-sourceOriginalQ0Scale r₀/30
  let HQ := sourceOriginalQActualHQ r₀ (jₓ L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)
  have hs : 0 < sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
    positivity
  have hd : d ≠ 0 := ne_of_gt (source_original_Q0_denominator_pos _ hs)
  have hRewrite := source_original_XA_prefactor_extract
    α c (Real.log (β/α)) γ δ d (Real.exp L) L HQ HP hd (ne_of_gt hL)
  dsimp [sourceOriginalXAGoodPrefactor, γ, δ, d, HQ, HP] at hRewrite
  dsimp only [sourceOriginalXAGoodPrefactor] at hh
  rw [hRewrite] at hh
  simpa only [sourceOriginalXAFixedConstant, k, ε] using hh



/- Exact source owner: SourceOriginalActualHarmonicControl.lean; original line 144. -/
theorem source_original_XA_literal_depth_lower_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant r₀ α β c *
        (Real.exp L/L) *
        (sourceOriginalQActualHQ r₀ (sourceOriginalLiteralDepth r₀ L) L *
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      sourceOriginalXA r₀
        (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  exact source_original_XA_fixed_parameter_lower_eventually
    r₀ hr₀ α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
    (sourceOriginalLiteralDepth r₀)
    ((source_original_literal_depth_properties_eventually r₀ hr₀).mono
      fun L h => h.2)



/- Exact source owner: SourceOriginalXAMassCompositionCore.lean; original line 46. -/
theorem source_original_XA_mass_constant_pos
    (α c logRatio γ δ d : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hlog : 0 < logRatio)
    (hγ : 0 < γ) (hδ : 0 < δ) (hd : 0 < d) :
    0 < sourceOriginalXAMassConstant α c logRatio γ δ d := by
  unfold sourceOriginalXAMassConstant
  positivity

/- The denominator occurring in the literal free-Q₀ theorem is
positive and simplifies to `(7/6) s` for positive source scale `s`. -/



/- Exact source owner: SourceOriginalXAFixedParameterLower.lean; original line 20. -/
theorem source_original_XA_fixed_constant_pos
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (α β c : ℝ)
    (hα : 1 < α) (hαβ : α < β) (hc : 0 < c) :
    0 < sourceOriginalXAFixedConstant r₀ α β c := by
  let ε := sourceOriginalFixedMacroEpsilon r₀
  have hε := source_original_fixed_macro_epsilon_pos r₀ hr₀
  have hεsmall := source_original_fixed_macro_epsilon_le_tenth r₀ hr₀
  have hγ : 0 < (sourceOriginalQUniformGamma ε)^((400*r₀)*r₀) := by
    have := (source_original_Q_uniform_gamma_positive_le_one
      ε (by simpa [ε] using hε) (by simpa [ε] using hεsmall)).1
    positivity
  have hδ : 0 < sourceOriginalPGroupParityDelta/2 :=
    div_pos source_original_P_group_parity_delta_positive (by norm_num)
  have hs : 0 < sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
    positivity
  have hd : 0 < (6/5:ℝ)*sourceOriginalQ0Scale r₀-
      sourceOriginalQ0Scale r₀/30 := source_original_Q0_denominator_pos _ hs
  have hlog : 0 < Real.log (β/α) := Real.log_pos
    ((one_lt_div (by linarith : 0 < α)).2 hαβ)
  unfold sourceOriginalXAFixedConstant
  dsimp only
  exact source_original_XA_mass_constant_pos _ _ _ _ _ _
    (by linarith) hc hlog hγ hδ hd

/- Fixed-parameter source XA lower bound along any moving depth with the
literal largest-admissible-index property.  This is the exact
`exp(L)/L * H_Q * H_P` lower normalization; no Type II premise occurs. -/


end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityActualXAMass221 -/

section

set_option maxHeartbeats 3000000
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Actual all-P harmonic normalization is positive for every true group,
including all groups in both original logarithmic windows. -/
theorem b635_actual_HP_one_le434 (r₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) := by
  filter_upwards [source_original_P_all_actual_local_eventually r₀] with L hLocal
  apply source_literal_HP_one_le
  · intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocal.2.1 g p hp)
  · exact hLocal.1

/-- The actual Parity mass lower bound, with an explicit fixed positive
constant and exactly the source exponent 221. The constant is fixed before
Type II accuracy and leaves every original weight and band untouched. -/
theorem b635_parity_actual_XA_lower_221434
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    0 < sourceOriginalXAFixedConstant 20 α β c ∧
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant 20 α β c * Real.exp L / L ^ (221:ℝ) ≤
        sourceOriginalXA 20
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
          (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ := by
  let K := sourceOriginalXAFixedConstant 20 α β c
  have hK : 0 < K := source_original_XA_fixed_constant_pos
    20 (by norm_num) α β c hα hαβ hc
  refine ⟨hK, ?_⟩
  filter_upwards [source_original_XA_literal_depth_lower_eventually
      20 (by norm_num) α β c Ψ hα hαβ hβ hc hΨnonneg hΨ,
    b635_parity_actual_HQ_lower_220434, b635_actual_HP_one_le434 20,
    eventually_gt_atTop (0:ℝ)] with L hXA hQ hP hL
  let HQ := sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands 20 L)
  have hHQ : 0 ≤ HQ := (Real.rpow_pos_of_pos hL (-220:ℝ)).le.trans hQ
  have hQHP : L ^ (-220:ℝ) ≤ HQ*HP := by
    calc
      L ^ (-220:ℝ) ≤ HQ := hQ
      _ = HQ*1 := by ring
      _ ≤ HQ*HP := mul_le_mul_of_nonneg_left hP hHQ
  have hEq : K * Real.exp L / L ^ (221:ℝ) =
      K * (Real.exp L/L) * L ^ (-220:ℝ) := by
    have hPow : L ^ (221:ℝ) = L * L ^ (220:ℝ) := by
      rw [show (221:ℝ) = 1+220 by norm_num, Real.rpow_add hL,
        Real.rpow_one]
    rw [hPow, Real.rpow_neg hL.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    K * Real.exp L / L ^ (221:ℝ) =
        K * (Real.exp L/L) * L ^ (-220:ℝ) := hEq
    _ ≤ K * (Real.exp L/L) * (HQ*HP) :=
      mul_le_mul_of_nonneg_left hQHP (by positivity)
    _ ≤ sourceOriginalXA 20
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
          (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ := hXA

theorem b635_original_cutoff_positive_interval434
    (Ψ : ℝ → ℝ) (hcont : Continuous Ψ)
    (hpos : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Ψ t) :
    ∃ α β c : ℝ, 1 < α ∧ α < β ∧ β < 2 ∧ 0 < c ∧
      ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t := by
  obtain ⟨t₀, ht1, ht2, htΨ⟩ := hpos
  have ho : IsOpen {t : ℝ | Ψ t₀ / 2 < Ψ t} :=
    isOpen_lt continuous_const hcont
  have hmem : t₀ ∈ {t : ℝ | Ψ t₀ / 2 < Ψ t} := by
    simp only [Set.mem_ofPred_eq]
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho t₀ hmem
  let η := min ε (min (t₀-1) (2-t₀)) / 4
  have hη : 0 < η := by
    dsimp [η]
    apply div_pos
    · apply lt_min hε
      exact lt_min (by linarith) (by linarith)
    · norm_num
  have hηε : η < ε := by
    have hh := min_le_left ε (min (t₀-1) (2-t₀))
    dsimp [η]
    linarith
  have hη1 : η < t₀-1 := by
    have hh := (min_le_right ε (min (t₀-1) (2-t₀))).trans
      (min_le_left (t₀-1) (2-t₀))
    dsimp [η]
    linarith
  have hη2 : η < 2-t₀ := by
    have hh := (min_le_right ε (min (t₀-1) (2-t₀))).trans
      (min_le_right (t₀-1) (2-t₀))
    dsimp [η]
    linarith
  refine ⟨t₀-η, t₀+η, Ψ t₀/2, by linarith, by linarith,
    by linarith, by linarith, ?_⟩
  intro t hα hβ
  have hdist : dist t t₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact (hball (Metric.mem_ball.mpr hdist)).le


/-- The original continuous nonnegative cutoff supplies the fixed positive
constant. No lower mass, sieve, character, or prime-pair estimate is assumed. -/
theorem b635_parity_original_cutoff_mass_221434
    (Ψ : ℝ → ℝ) (hcont : Continuous Ψ)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hpos : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Ψ t) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      K*x/(Real.log x)^(221:ℝ) ≤
        sourceOriginalXA 20
          (sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 (Real.log x)) (Real.log x))
          (sourceOriginalPAllActualBands 20 (Real.log x)) x Ψ := by
  obtain ⟨α, β, c, hα, hαβ, hβ, hc, hΨ⟩ :=
    b635_original_cutoff_positive_interval434 Ψ hcont hpos
  have h := b635_parity_actual_XA_lower_221434
    α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
  refine ⟨sourceOriginalXAFixedConstant 20 α β c, h.1, ?_⟩
  have hx := Real.tendsto_log_atTop.eventually h.2
  filter_upwards [hx, eventually_gt_atTop (0:ℝ)] with x hh hxp
  simpa only [Real.exp_log hxp] using hh

/-- A genuinely populated original negative-parity candidate class at
every sufficiently large scale, obtained from the quantitative actual mass.
This is an unconditioned marked-weight witness; primality of u+2 remains
the separate sieve obligation. -/
theorem b635_parity_original_positive_candidate434
    (Ψ : ℝ → ℝ) (hcont : Continuous Ψ)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hpos : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Ψ t) :
    ∀ᶠ x : ℝ in atTop, ∃ u : ℕ,
      u ∈ Finset.range (⌊2*x⌋₊+1) ∧
      0 < sourceOriginalA 20
        (sourceOriginalQActualBands 20
          (sourceOriginalLiteralDepth 20 (Real.log x)) (Real.log x))
        (sourceOriginalPAllActualBands 20 (Real.log x)) u ∧
      0 < Ψ ((u:ℝ)/x) ∧ ArithmeticFunction.liouville u = -1 := by
  obtain ⟨K,hK,hMass⟩ :=
    b635_parity_original_cutoff_mass_221434 Ψ hcont hΨnonneg hpos
  filter_upwards [hMass, eventually_gt_atTop (1:ℝ)] with x hMassx hx
  have hxp : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hXA : 0 < sourceOriginalXA 20
      (sourceOriginalQActualBands 20
        (sourceOriginalLiteralDepth 20 (Real.log x)) (Real.log x))
      (sourceOriginalPAllActualBands 20 (Real.log x)) x Ψ :=
    (div_pos (mul_pos hK hxp) (Real.rpow_pos_of_pos hlog _)).trans_le hMassx
  unfold sourceOriginalXA at hXA
  let Q := sourceOriginalQActualBands 20
    (sourceOriginalLiteralDepth 20 (Real.log x)) (Real.log x)
  let P := sourceOriginalPAllActualBands 20 (Real.log x)
  have hSome : ∃ u ∈ Finset.range (⌊2*x⌋₊+1),
      0 < sourceOriginalA 20 Q P u * Ψ ((u:ℝ)/x) := by
    by_contra hh
    push Not at hh
    have hs : (∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        sourceOriginalA 20 Q P u * Ψ ((u:ℝ)/x)) ≤ 0 :=
      Finset.sum_nonpos hh
    exact (not_lt_of_ge hs) hXA
  obtain ⟨u,hu,hWeight⟩ := hSome
  have hA : 0 < sourceOriginalA 20 Q P u := by
    by_contra hh
    have hh' : sourceOriginalA 20 Q P u ≤ 0 := le_of_not_gt hh
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg hh' (hΨnonneg ((u:ℝ)/x))
    linarith
  have hPsi : 0 < Ψ ((u:ℝ)/x) :=
    (mul_pos_iff_of_pos_left hA).1 hWeight
  have hPodd : Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) u) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hz : sourceOriginalA 20 Q P u = 0 := by
      rw [sourceOriginalA, he.neg_one_pow]
      ring
    linarith
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz,sourceOriginalPParityExponent] at hPodd
  have hc : sourceOriginalOrdinaryCoefficient 20 Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) ≠ 0 := by
    intro hz
    have ha0 : sourceOriginalA 20 Q P u = 0 := by
      rw [sourceOriginalA, sourceOriginalA0, hz]
      ring
    linarith
  have hLiouville := Green64Analytic.Parity.b628_parity_liouville_equals_P_phase434 Q P u hu0
    (source_original_Q_actual_prime 20 _ _) hc
  rw [hPodd.neg_one_pow] at hLiouville
  exact ⟨u,hu,hA,hPsi,hLiouville⟩

end Green64Analytic.SourceBlockSieve

end

/-! ## ParitySourceDisintegration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

def parityOriginalParitySign434 (parityFlag : Bool) : ℝ :=
  if parityFlag then 1 else -1

/-- The genuine source projector, with all prime-power multiplicities.
False selects rho=-1, true selects rho=+1. -/
theorem parity_original_parity_projection_eq_indicator434
    (parityFlag : Bool) (Pall : Finset ℕ) (u : ℕ) :
    (1 + parityOriginalParitySign434 parityFlag *
        (-1:ℝ)^sourceOriginalPParityExponent Pall u)/2 =
      if decide (Odd (sourceOriginalPParityExponent Pall u)) ≠ parityFlag
      then 1 else 0 := by
  rcases Nat.even_or_odd (sourceOriginalPParityExponent Pall u) with he | ho
  · have hno : ¬Odd (sourceOriginalPParityExponent Pall u) :=
      Nat.not_odd_iff_even.mpr he
    cases parityFlag <;> norm_num [parityOriginalParitySign434,he.neg_one_pow,hno]
  · cases parityFlag <;> norm_num [parityOriginalParitySign434,ho.neg_one_pow,ho]

theorem parity_original_parity_projection_zero_or_one434
    (parityFlag : Bool) (Pall : Finset ℕ) (u : ℕ) :
    (1 + parityOriginalParitySign434 parityFlag *
        (-1:ℝ)^sourceOriginalPParityExponent Pall u)/2 = 0 ∨
    (1 + parityOriginalParitySign434 parityFlag *
        (-1:ℝ)^sourceOriginalPParityExponent Pall u)/2 = 1 := by
  rw [parity_original_parity_projection_eq_indicator434]
  split_ifs <;> simp

/-- Both source A_rho weights, before introducing any signed analytic sum. -/
def parityOriginalParityA434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (u : ℕ) : ℝ :=
  sourceOriginalA0 r Q P u *
    ((1 + parityOriginalParitySign434 parityFlag *
      (-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u)/2)

/-- Literal finite X_rho, with the original floor(2x) cutoff. -/
def parityOriginalParityXA434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
    parityOriginalParityA434 parityFlag r Q P u * Ψ ((u:ℝ)/x)

noncomputable def parityOriginalParityQSamplingWeight434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (P : G → Finset ℕ) (u : ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
    sourceOriginalW1 P u *
    ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
       (Finset.univ.biUnion P) u)/2) * Ψ ((u:ℝ)/x)
/- This conditions the LITERAL source X_A on one labelled Q slot,
not an auxiliary normalized law. The orbit membership is left
explicit rather than silently assuming completeness of a fiber. -/

theorem parity_original_XA_complete_orbit_finite_sampling_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        ∑ f ∈ sourceOriginalFullQOrbitAt r Q
              (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u),
          (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
            sourceOriginalW1 P u *
            ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
                 (Finset.univ.biUnion P) u)/2) *
            Ψ ((u:ℝ)/x) := by
  classical
  unfold parityOriginalParityXA434
  apply Finset.sum_congr rfl
  intro u hu
  rw [parityOriginalParityA434, sourceOriginalA0,
    source_original_full_Q_coefficient_finite_sampling
      r Q _ hPrime hDisjoint]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  ring

theorem parity_original_QP_fibre_sampling_weight_exact_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P))
    (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    let q : ℕ := ∏ b : B, ∏ i : Fin r, (f b i).val
    sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (q*R.val) = q ∧
    parityOriginalParityQSamplingWeight434 parityFlag (B:=B) r P (q*R.val) x Ψ =
      (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
           (Finset.univ.biUnion P) R.val)/2) *
        Ψ (((q*R.val:ℕ):ℝ)/x) := by
  classical
  intro q
  let Pall := Finset.univ.biUnion P
  have hqNonzero : q ≠ 0 := by
    dsimp [q]
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (hQPrime b _ (f b i).property).ne_zero
  have hNo := source_original_full_Q_product_no_P_prime
    r Q P f hQPrime hPPrime hQP
  have hAllPrime : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g, hg, hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPPrime g p hpg
  have hOrd : sourceOriginalOrdinaryPart Pall (q*R.val) = q :=
    source_original_QP_ordinary_part_product Pall q R
      hqNonzero hAllPrime hNo
  have hWeight := source_original_full_Q_product_P_weight_invariant
    r Q P f R.val R.property.1 hQPrime hPPrime hQP
  refine ⟨hOrd, ?_⟩
  change (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
    sourceOriginalW1 P (q*R.val) *
    ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
       Pall (q*R.val))/2) * Ψ (((q*R.val:ℕ):ℝ)/x) = _
  rw [hWeight.1, hWeight.2]

theorem parity_original_XA_full_QP_tsum_disintegration_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
      ∑ f : (b : B) → Fin r → {p // p ∈ Q b},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          if (∏ b : B, ∏ i : Fin r, (f b i).val) * R.val < ⌊2*x⌋₊+1
          then parityOriginalParityQSamplingWeight434 parityFlag (B:=B) r P
            ((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) x Ψ
          else 0 := by
  classical
  let A := (b : B) → Fin r → {p // p ∈ Q b}
  let Pall : Finset ℕ := Finset.univ.biUnion P
  let N : ℕ := ⌊2*x⌋₊+1
  let q (f : A) : ℕ := ∏ b : B, ∏ i : Fin r, (f b i).val
  let w (u : ℕ) : ℝ := parityOriginalParityQSamplingWeight434 parityFlag (B:=B) r P u x Ψ
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g, hg, hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPPrime g p hpg
  have hw0 : w 0 = 0 := by
    simp [w, parityOriginalParityQSamplingWeight434, hΨzero]
  have hFibre (u : ℕ) :
      (∑ f ∈ sourceOriginalFullQOrbitAt r Q
        (sourceOriginalOrdinaryPart Pall u), w u) =
      ∑ f : A, if q f = sourceOriginalOrdinaryPart Pall u
        then w u else 0 := by
    calc
      _ = ∑ f : A, if f ∈ sourceOriginalFullQOrbitAt r Q
        (sourceOriginalOrdinaryPart Pall u) then w u else 0 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro f hf
        have hIff := source_original_full_Q_canonical_orbit_iff_product
          r Q (sourceOriginalOrdinaryPart Pall u) f hQPrime hQDisj
        by_cases h : f ∈ sourceOriginalFullQOrbitAt r Q
          (sourceOriginalOrdinaryPart Pall u)
        · simp [h, hIff.mp h, q]
        · simp [h, hIff.not.mp h, q]
  calc
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
        ∑ u ∈ Finset.range N,
          ∑ f : A, if q f = sourceOriginalOrdinaryPart Pall u
            then w u else 0 := by
              rw [parity_original_XA_complete_orbit_finite_sampling_parity434 parityFlag
                r Q P x Ψ hQPrime hQDisj]
              change (∑ u ∈ Finset.range N,
                ∑ f ∈ sourceOriginalFullQOrbitAt r Q
                  (sourceOriginalOrdinaryPart Pall u), w u) = _
              apply Finset.sum_congr rfl
              intro u hu
              exact hFibre u
    _ = ∑ f : A, ∑ u ∈ Finset.range N,
        if sourceOriginalOrdinaryPart Pall u = q f then w u else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro f hf
          apply Finset.sum_congr rfl
          intro u hu
          by_cases h : q f = sourceOriginalOrdinaryPart Pall u
          · simp [h]
          · have h' : sourceOriginalOrdinaryPart Pall u ≠ q f := Ne.symm h
            simp [h, h']
    _ = ∑ f : A,
        ∑' R : sourceOriginalPSupported Pall,
          if (q f) * R.val < N then w ((q f)*R.val) else 0 := by
            apply Finset.sum_congr rfl
            intro f hf
            have hq : q f ≠ 0 := by
              dsimp [q]
              apply Finset.prod_ne_zero_iff.mpr
              intro b hb
              apply Finset.prod_ne_zero_iff.mpr
              intro i hi
              exact (hQPrime b _ (f b i).property).ne_zero
            have hNo : ∀ p ∈ Pall, ¬p ∣ q f :=
              source_original_full_Q_product_no_P_prime
                r Q P f hQPrime hPPrime hQP
            exact source_original_QP_fibre_finite_tsum
              Pall (q f) N w hq hAll hNo hw0
    _ = _ := rfl

theorem parity_original_XA_QP_literal_weights_exact_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
      ∑ f : (b : B) → Fin r → {p // p ∈ Q b},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          if (∏ b : B, ∏ i : Fin r, (f b i).val) * R.val < ⌊2*x⌋₊+1
          then (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
            sourceOriginalW1 P R.val *
            ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion P) R.val)/2) *
            Ψ (((((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) : ℕ) : ℝ) / x)
          else 0 := by
  rw [parity_original_XA_full_QP_tsum_disintegration_parity434 parityFlag
    r Q P x Ψ hΨzero hQPrime hQDisj hPPrime hQP]
  apply Finset.sum_congr rfl
  intro f hf
  apply tsum_congr
  intro R
  split_ifs with hCut
  · exact (parity_original_QP_fibre_sampling_weight_exact_parity434 parityFlag
      r Q P f R x Ψ hQPrime hPPrime hQP).2
  · rfl

noncomputable def parityOriginalParityQPLiteralTerm434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
  (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
    sourceOriginalW1 P R.val *
    ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
      (Finset.univ.biUnion P) R.val)/2) *
    Ψ (((((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) : ℕ) : ℝ) / x)

/- Every literal term is nonnegative under the source's
nonnegative cutoff, without changing multiplicity parity. -/

theorem parity_original_QP_literal_term_nonneg_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) (hΨ : ∀ t, 0 ≤ Ψ t)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    0 ≤ parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R := by
  have hParity : 0 ≤
      (1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2 := by
    rcases parity_original_parity_projection_zero_or_one434 parityFlag
      (Finset.univ.biUnion P) R.val with hh | hh
    · rw [hh]
    · rw [hh]
      norm_num
  unfold parityOriginalParityQPLiteralTerm434
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity)
      (source_original_W1_nonneg P R.val)) hParity) (hΨ _)
/- Any genuine Q×P good event gives a lower sub-sum for original X_A.
This is actual pruning of the exact full weighted disintegration,
not an assumed mass lower bound for the good event. -/
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityFreeSlotSource -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- Exact original free-Q-slot disintegration and localization for BOTH
parity projections. The original Q tuple, all factorials, positive P-supported
integer, sharp finite u cutoff, and unsmoothed Psi factors are retained. -/
theorem parity_original_XA_full_QP_free_slot_exact_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
      ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        ∑ p : {p // p ∈ Q b},
          ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
            let f := (sourceOriginalQSlotsCurryEquiv r Q)
              ((Equiv.piSplitAt (b,i)
                (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
                (p,rest))
            if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
            then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0 := by
  classical
  let A := (j : B) → Fin r → {p // p ∈ Q j}
  let S := (k : B × Fin r) → {p // p ∈ Q k.1}
  let e : S ≃ A := sourceOriginalQSlotsCurryEquiv r Q
  let w (f : A) : ℝ :=
    ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
      then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0
  calc
    parityOriginalParityXA434 parityFlag r Q P x Ψ = ∑ f : A, w f := by
      simpa only [w, parityOriginalParityQPLiteralTerm434, A] using
        parity_original_XA_QP_literal_weights_exact_parity434 parityFlag
          r Q P x Ψ hΨzero hQPrime hQDisj hPPrime hQP
    _ = ∑ g : S, w (e g) := (Equiv.sum_comp e w).symm
    _ = ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
          ∑ p : {p // p ∈ Q b},
            w (e ((Equiv.piSplitAt (b,i)
              (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
              (p,rest))) :=
        source_full_Q_one_free_slot_sum r Q b i (fun g : S => w (e g))
    _ = _ := rfl

theorem parity_original_XA_QP_free_prime_inside_P_tsum_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    parityOriginalParityXA434 parityFlag r Q P x Ψ =
      ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          ∑ p : {p // p ∈ Q b},
            let f := (sourceOriginalQSlotsCurryEquiv r Q)
              ((Equiv.piSplitAt (b,i)
                (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
                (p,rest))
            if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
            then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0 := by
  classical
  rw [parity_original_XA_full_QP_free_slot_exact_parity434 parityFlag
    r Q P b i x Ψ hΨzero hQPrime hQDisj hPPrime hQP]
  apply Finset.sum_congr rfl
  intro rest hrest
  let e := sourceOriginalQSlotsCurryEquiv r Q
  let t (p : {p // p ∈ Q b}) :=
    e ((Equiv.piSplitAt (b,i)
      (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  let q (p : {p // p ∈ Q b}) : ℕ :=
    ∏ j : B, ∏ m : Fin r, (t p j m).val
  let F (p : {p // p ∈ Q b})
      (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
    parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ (t p) R
  have hq (p : {p // p ∈ Q b}) : 0 < q p := by
    apply Nat.pos_of_ne_zero
    dsimp [q]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact (hQPrime j _ (t p j m).property).ne_zero
  change (∑ p : {p // p ∈ Q b},
      ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
        if q p * R.val < ⌊2*x⌋₊+1 then F p R else 0) =
    ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      ∑ p : {p // p ∈ Q b},
        if q p * R.val < ⌊2*x⌋₊+1 then F p R else 0
  exact source_original_QP_finite_prime_P_tsum_comm
    (Finset.univ.biUnion P) (⌊2*x⌋₊+1) q hq F

theorem parity_original_XA_QP_free_prime_term_factor_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    let n : ℕ :=
      (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) * R.val
    let C : ℝ :=
      (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)
    (∑ p : {p // p ∈ Q b},
      let f := (sourceOriginalQSlotsCurryEquiv r Q)
        ((Equiv.piSplitAt (b,i)
          (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
      if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
      then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0) =
    C * (∑ p ∈ Q b,
      if p*n < ⌊2*x⌋₊+1
      then Ψ (((p*n:ℕ):ℝ)/x) else 0) := by
  classical
  intro n C
  let f (p : {p // p ∈ Q b}) :=
    (sourceOriginalQSlotsCurryEquiv r Q)
      ((Equiv.piSplitAt (b,i)
        (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  have hprod (p : {p // p ∈ Q b}) :
      (∏ j : B, ∏ m : Fin r, (f p j m).val) * R.val =
        p.val*n := by
    rw [source_original_Q_free_slot_product_exact r Q b i p rest]
    dsimp [n]
    ring
  have hterm (p : {p // p ∈ Q b}) :
      parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ (f p) R =
        C * Ψ ((((p.val*n:ℕ):ℝ))/x) := by
    unfold parityOriginalParityQPLiteralTerm434
    rw [source_original_Q_free_slot_product_exact r Q b i p rest]
    rw [show (p.val *
      (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val)) * R.val =
      p.val*n by dsimp [n]; ring]
  calc
    _ = ∑ p : {p // p ∈ Q b},
      C * (if p.val*n < ⌊2*x⌋₊+1
        then Ψ ((((p.val*n:ℕ):ℝ))/x) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          change (if (∏ j : B, ∏ m : Fin r, (f p j m).val) *
            R.val < ⌊2*x⌋₊+1
            then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ (f p) R
            else 0) = _
          rw [hprod p, hterm p]
          split_ifs <;> ring
    _ = C * ∑ p : {p // p ∈ Q b},
        (if p.val*n < ⌊2*x⌋₊+1
         then Ψ ((((p.val*n:ℕ):ℝ))/x) else 0) := by
           rw [Finset.mul_sum]
    _ = C * (∑ p ∈ Q b,
        if p*n < ⌊2*x⌋₊+1
        then Ψ (((p*n:ℕ):ℝ)/x) else 0) := by
          exact congrArg (fun y : ℝ => C*y)
            (Finset.sum_coe_sort (Q b) (fun p : ℕ =>
              if p*n < ⌊2*x⌋₊+1
              then Ψ (((p*n:ℕ):ℝ)/x) else 0))

theorem parity_original_Q0_actual_XA_free_prime_floor_eventually_parity434 (parityFlag : Bool)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (α β c : ℝ) (Ψ : ℝ → ℝ)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
      (Q : B → Finset ℕ) (P : G → Finset ℕ)
      (b : B) (i : Fin r₀)
      (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
      (hQ0 : Q b = sourceClosedPrimeLogBand L
        (sourceOriginalQ0Scale r₀)
        ((6/5:ℝ)*sourceOriginalQ0Scale r₀))
      (rest : (k : {k : B × Fin r₀ // k ≠ (b,i)}) →
            {p // p ∈ Q k.1.1})
      (R : sourceOriginalPSupported (Finset.univ.biUnion P)),
      let n : ℕ :=
        (∏ k : {k : B × Fin r₀ // k ≠ (b,i)}, (rest k).val) * R.val
      let C : ℝ :=
        (∏ _b : B, (1:ℝ)/(r₀.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)
      L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L-
        sourceOriginalQ0Scale r₀*L/30 ≤ Real.log (n:ℝ) →
      Real.log (n:ℝ) ≤
        L-(11/10:ℝ)*sourceOriginalQ0Scale r₀*L+
          sourceOriginalQ0Scale r₀*L/30 →
      C * ((α*Real.exp L/(n:ℝ)) *
        (c*Real.log (β/α)/
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L))) ≤
      ∑ p : {p // p ∈ Q b},
        let f := (sourceOriginalQSlotsCurryEquiv r₀ Q)
          ((Equiv.piSplitAt (b,i)
            (fun k : B × Fin r₀ => {p // p ∈ Q k.1})).symm (p,rest))
        if (∏ j : B, ∏ m : Fin r₀, (f j m).val) * R.val <
            ⌊2*Real.exp L⌋₊+1
        then parityOriginalParityQPLiteralTerm434 parityFlag r₀ Q P (Real.exp L) Ψ f R else 0 := by
  have hCount := source_original_Q0_good_rest_count_with_u_cutoff
    r₀ hr₀ α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hCount] with L hCountL
  intro B G hFinB hDecB hFinG Q P b i hQPrime hQ0 rest R n C hLo hHi
  have hRestProd : 0 <
      (∏ k : {k : B × Fin r₀ // k ≠ (b,i)}, (rest k).val) := by
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact (hQPrime k.val.1 _ (rest k).property).ne_zero
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos hRestProd (Nat.pos_of_ne_zero R.property.1)
  have hFloor := hCountL n hn hLo hHi
  rw [← hQ0] at hFloor
  have hParity : 0 ≤
      (1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2 := by
    rcases parity_original_parity_projection_zero_or_one434 parityFlag
      (Finset.univ.biUnion P) R.val with hh | hh
    · rw [hh]
    · rw [hh]
      norm_num
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) (source_original_W1_nonneg P R.val)) hParity
  have hFactor := parity_original_XA_QP_free_prime_term_factor_parity434 parityFlag
    r₀ Q P b i (Real.exp L) Ψ rest R
  change C * _ ≤ _
  rw [hFactor]
  exact mul_le_mul_of_nonneg_left hFloor hC

noncomputable def parityOriginalParityQPActualFreeTerm434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
  ∑ p : {p // p ∈ Q b},
    let f := (sourceOriginalQSlotsCurryEquiv r Q)
      ((Equiv.piSplitAt (b,i)
        (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
    if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
    then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0

/- The true conditional free-prime term is nonnegative for source Psi. -/

theorem parity_original_QP_actual_free_term_nonneg_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ t, 0 ≤ Ψ t)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    0 ≤ parityOriginalParityQPActualFreeTerm434 parityFlag r Q P b i x Ψ rest R := by
  unfold parityOriginalParityQPActualFreeTerm434
  apply Finset.sum_nonneg
  intro p hp
  let f := (sourceOriginalQSlotsCurryEquiv r Q)
    ((Equiv.piSplitAt (b,i)
      (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  change 0 ≤ (if (∏ j : B, ∏ m : Fin r, (f j m).val)*R.val < ⌊2*x⌋₊+1
    then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0)
  split_ifs with hc
  · exact parity_original_QP_literal_term_nonneg_parity434 parityFlag r Q P x Ψ hΨ _ R
  · exact le_rfl

/- Even after summing the free Q-prime, the original u cutoff
forces finite support in the true positive P-supported variable. -/

theorem parity_original_QP_actual_free_term_summable_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1}) :
    Summable (parityOriginalParityQPActualFreeTerm434 parityFlag r Q P b i x Ψ rest) := by
  let N : ℕ := ⌊2*x⌋₊+1
  apply summable_of_hasFiniteSupport
  apply (source_original_P_bounded_finite (Finset.univ.biUnion P) N).subset
  intro R hSupport
  by_contra hNot
  have hRbig : N ≤ R.val := Nat.le_of_not_gt hNot
  have hZero : parityOriginalParityQPActualFreeTerm434 parityFlag r Q P b i x Ψ rest R = 0 := by
    unfold parityOriginalParityQPActualFreeTerm434
    apply Finset.sum_eq_zero
    intro p hp
    let f := (sourceOriginalQSlotsCurryEquiv r Q)
       ((Equiv.piSplitAt (b,i)
          (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
    have hq : 0 < (∏ j : B, ∏ m : Fin r, (f j m).val) := by
      apply Nat.pos_of_ne_zero
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      apply Finset.prod_ne_zero_iff.mpr
      intro m hm
      exact (hQPrime j _ (f j m).property).ne_zero
    have hmul : R.val ≤
        (∏ j : B, ∏ m : Fin r, (f j m).val)*R.val :=
      Nat.le_mul_of_pos_left R.val hq
    have hOff : ¬(∏ j : B, ∏ m : Fin r, (f j m).val)*R.val < N :=
      Nat.not_lt.mpr (hRbig.trans hmul)
    change (if (∏ j : B, ∏ m : Fin r, (f j m).val)*R.val < N
      then parityOriginalParityQPLiteralTerm434 parityFlag r Q P x Ψ f R else 0) = 0
    simp [hOff]
  exact hSupport hZero

/- Original XA dominates every genuine rest×P good event, after the
free Q slot has been summed. No good-mass positivity is postulated. -/

theorem parity_original_XA_QP_good_rest_lower_parity434 (parityFlag : Bool)
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hΨ : ∀ t, 0 ≤ Ψ t)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False)
    (Good : ((k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1}) →
      sourceOriginalPSupported (Finset.univ.biUnion P) → Prop) :
    (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1},
       ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
         if Good rest R then
           parityOriginalParityQPActualFreeTerm434 parityFlag r Q P b i x Ψ rest R else 0) ≤
    parityOriginalParityXA434 parityFlag r Q P x Ψ := by
  classical
  rw [parity_original_XA_QP_free_prime_inside_P_tsum_parity434 parityFlag
    r Q P b i x Ψ hΨzero hQPrime hQDisj hPPrime hQP]
  apply Finset.sum_le_sum
  intro rest hrest
  let v : sourceOriginalPSupported (Finset.univ.biUnion P) → ℝ :=
    parityOriginalParityQPActualFreeTerm434 parityFlag r Q P b i x Ψ rest
  have hNonneg (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
      0 ≤ v R :=
    parity_original_QP_actual_free_term_nonneg_parity434 parityFlag r Q P b i x Ψ hΨ rest R
  have hFull : Summable v :=
    parity_original_QP_actual_free_term_summable_parity434 parityFlag
      r Q P b i x Ψ hQPrime rest
  have hLe (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
      (if Good rest R then v R else 0) ≤ v R := by
    split_ifs <;> [exact le_rfl; exact hNonneg R]
  have hRestricted : Summable (fun R : sourceOriginalPSupported
      (Finset.univ.biUnion P) => if Good rest R then v R else 0) :=
    hFull.of_nonneg_of_le (fun R => by split_ifs <;> [exact hNonneg R; exact le_rfl]) hLe
  change (∑' R, if Good rest R then v R else 0) ≤ ∑' R, v R
  exact Summable.tsum_le_tsum hLe hRestricted hFull
end Green64Analytic.SourceBlockSieve

end

end

