module

public import Green64.Library.Weights.Part104

@[expose] public section

/-!
# Weights / Part105

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Mass006 -/

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


/- Exact source owner: SourceOriginalQBandUniformCap.lean; original line 11. -/
theorem source_original_Q_actual_band_harmonic_le_four
    (r₀ jₓ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (j : Fin (jₓ+1))
    (ht : 2 ≤ sourceOriginalQActualExponent r₀ j.val * L) :
    (∑ p ∈ sourceOriginalQActualBands r₀ jₓ L j,
        (p:ℝ)⁻¹) ≤ 4 := by
  let t : ℝ := sourceOriginalQActualExponent r₀ j.val * L
  let w : ℝ := Real.exp ((3/4:ℝ)*t)
  have htPos : 0 < t := by dsimp [t] at *; linarith
  have hw : 1 < w := by
    dsimp [w]
    rw [← Real.exp_zero]
    exact Real.exp_strictMono (by nlinarith)
  have hPrime (p : ℕ)
      (hp : p ∈ sourceOriginalQActualBands r₀ jₓ L j) :
      p.Prime := source_original_Q_actual_prime r₀ jₓ L j p hp
  have hRange (p : ℕ)
      (hp : p ∈ sourceOriginalQActualBands r₀ jₓ L j) :
      Real.exp t ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp ((6/5:ℝ)*t) := by
    change Real.exp (sourceOriginalQActualExponent r₀ j.val * L) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp ((6/5:ℝ) *
        (sourceOriginalQActualExponent r₀ j.val * L))
    rw [source_original_Q_actual_scale_eq_P_scale r₀ j.val L hr₀]
    exact source_original_Q_actual_prime_range r₀ jₓ L hr₀ j p hp
  have hLower : w < Real.exp t := by
    dsimp [w]
    exact Real.exp_strictMono (by nlinarith)
  have hUpper : Real.exp ((6/5:ℝ)*t) ≤ Real.exp ((3/2:ℝ)*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hSq : w^2 = Real.exp ((3/2:ℝ)*t) := by
    dsimp [w]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply source_quadratic_prime_reciprocal_le_four w
    (sourceOriginalQActualBands r₀ jₓ L j) hw
  intro p hp
  have hr := hRange p hp
  exact ⟨hPrime p hp, hLower.trans_le hr.1,
    (hr.2.trans hUpper).trans_eq hSq.symm⟩



/- Exact source owner: SourceOriginalQRestHarmonicExact.lean; original line 28. -/
theorem source_original_Q_product_split_one_real
    {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (v : I → ℝ) :
    (∏ k : I, v k) =
      v i * ∏ k : {k : I // k ≠ i}, v k.val := by
  classical
  calc
    (∏ k : I, v k) =
        v i * ∏ k ∈ (Finset.univ.erase i), v k :=
          (Finset.mul_prod_erase Finset.univ v (Finset.mem_univ i)).symm
    _ = v i * ∏ k : {k : I // k ≠ i}, v k.val := by
      rw [Finset.prod_subtype (p := fun k : I => k ≠ i)
        (Finset.univ.erase i) (by intro k; simp) v]

/- EXACT source harmonic disintegration: one original labelled prime
has V_(Q_b) mass, and its remaining slots have the full factorial
harmonic rest mass. This is the Q part of the wt:expectation identity. -/


end Green64Analytic.SourceBlockSieve

namespace Green64FiniteExtraction


/- Exact source owner: Assignments.lean; original line 21. -/
theorem assignment_reciprocal :
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (c : ℝ),
    (∑ a : (i : ι) → {p // p ∈ P i}, c / ((∏ i, (a i).val : ℕ) : ℝ)) =
      c * ∏ i, ∑ p ∈ P i, (p : ℝ)⁻¹ :=
by
 classical
 intro ι _ _ P c
 have hpi :
     (∑ a : (i : ι) → {p // p ∈ P i}, ∏ i, ((a i).val : ℝ)⁻¹) =
       ∏ i, ∑ p ∈ P i, (p : ℝ)⁻¹ := by
   have hh := Finset.prod_univ_sum
     (fun i : ι => (Finset.univ : Finset {p // p ∈ P i}))
     (fun i p => (p.val : ℝ)⁻¹)
   rw [Fintype.piFinset_univ] at hh
   calc
     _ = ∏ i, ∑ p : {p // p ∈ P i}, (p.val : ℝ)⁻¹ := hh.symm
     _ = _ := by
       apply Finset.prod_congr rfl
       intro i hi
       exact Finset.sum_attach (P i) (fun p => (p : ℝ)⁻¹)
 calc
   _ = ∑ a : (i : ι) → {p // p ∈ P i}, c * ∏ i, ((a i).val : ℝ)⁻¹ := by
     apply Finset.sum_congr rfl
     intro a ha
     simp [div_eq_mul_inv]
   _ = c * ∑ a : (i : ι) → {p // p ∈ P i}, ∏ i, ((a i).val : ℝ)⁻¹ := by
     rw [Finset.mul_sum]
   _ = _ := by rw [hpi]

/- Exact proposition checked by source-assignment-mass-03. See the paired request and receipt. -/


end Green64FiniteExtraction

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceOriginalQRestHarmonicExact.lean; original line 11. -/
theorem source_original_Q_rest_harmonic_mass_exact
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) :
    (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
       {p // p ∈ Q k.1.1},
      (∏ _b : B, (r.factorial:ℝ)⁻¹) /
        (((∏ k : {k : B × Fin r // k ≠ (b,i)},
          (rest k).val):ℕ):ℝ)) =
    (∏ _b : B, (r.factorial:ℝ)⁻¹) *
      (∏ k : {k : B × Fin r // k ≠ (b,i)},
        ∑ p ∈ Q k.val.1, (p:ℝ)⁻¹) := by
  classical
  exact Green64FiniteExtraction.assignment_reciprocal
    (fun k : {k : B × Fin r // k ≠ (b,i)} => Q k.val.1)
    (∏ _b : B, (r.factorial:ℝ)⁻¹)

/- A generic coefficient product splits off its one fixed labelled slot. -/



/- Exact source owner: SourceOriginalQRestHarmonicExact.lean; original line 45. -/
theorem source_original_Q_full_harmonic_eq_free_times_rest
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) :
    (∑ f : (k : B × Fin r) → {p // p ∈ Q k.1},
      (∏ _b : B, (r.factorial:ℝ)⁻¹) /
        (((∏ k : B × Fin r, (f k).val):ℕ):ℝ)) =
    (∑ p ∈ Q b, (p:ℝ)⁻¹) *
      (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        (∏ _b : B, (r.factorial:ℝ)⁻¹) /
          (((∏ k : {k : B × Fin r // k ≠ (b,i)},
            (rest k).val):ℕ):ℝ)) := by
  classical
  let C : ℝ := ∏ _b : B, (r.factorial:ℝ)⁻¹
  let V : B × Fin r → ℝ := fun k => ∑ p ∈ Q k.1, (p:ℝ)⁻¹
  have hAll := Green64FiniteExtraction.assignment_reciprocal
    (fun k : B × Fin r => Q k.1) C
  have hRest := source_original_Q_rest_harmonic_mass_exact r Q b i
  have hSplit := source_original_Q_product_split_one_real (b,i) V
  calc
    _ = C * (∏ k : B × Fin r, V k) := by simpa only [C, V] using hAll
    _ = V (b,i) *
      (C * (∏ k : {k : B × Fin r // k ≠ (b,i)}, V k.val)) := by
        rw [hSplit]
        ring
    _ = _ := by
      rw [← hRest]



/- Exact source owner: SourceOriginalQ0RestMassCap.lean; original line 12. -/
theorem source_original_Q0_labelled_HQ_le_four_rest
    (r₀ jₓ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (ht : 2 ≤ sourceOriginalQActualExponent r₀ 0 * L)
    (i : Fin r₀) :
    (∑ f : (z : Fin (jₓ+1) × Fin r₀) →
      {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.1},
      (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
        (((∏ z, (f z).val):ℕ):ℝ)) ≤
    4 * sourceOriginalQActualRestHarmonicMass r₀ jₓ L
      ⟨0,Nat.succ_pos jₓ⟩ i := by
  classical
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  have hV : (∑ p ∈ Q b,(p:ℝ)⁻¹) ≤ 4 :=
    source_original_Q_actual_band_harmonic_le_four r₀ jₓ L hr₀ b
      (by simpa [b] using ht)
  have hRest : 0 ≤ sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i := by
    unfold sourceOriginalQActualRestHarmonicMass
    apply Finset.sum_nonneg
    intro rest hrest
    positivity
  have hIdentity := source_original_Q_full_harmonic_eq_free_times_rest
    r₀ Q b i
  change (∑ f : (z : Fin (jₓ+1) × Fin r₀) → {p // p ∈ Q z.1},
      (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
        (((∏ z, (f z).val):ℕ):ℝ)) ≤ _
  calc
    _ = (∑ p ∈ Q b, (p:ℝ)⁻¹) *
        sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i := hIdentity
    _ ≤ 4 * sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i :=
      mul_le_mul_of_nonneg_right hV hRest



/- Exact source owner: SourceOriginalQJointMidpoint.lean; original line 22. -/
noncomputable def sourceOriginalQJointRestGamma
    (r₀ jₓ k : ℕ) (ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) : ℝ :=
  let s := sourceOriginalQActualExponent r₀ z.val.1.val
  if z.val.1.val < k then
    Real.log (((11/10+ε)*s)/((11/10-ε)*s))/16
  else 1

/- Joint harmonic restriction in the ACTUAL original Q_j family.
All macro midpoint constraints hold simultaneously, while every
micro slot remains unrestricted; the cost is precisely the product
of the proven local harmonic fractions (no probability axiom). -/



/- Exact source owner: SourceOriginalQMacroSlotCount.lean; original line 10. -/
theorem source_original_Q_fixed_macro_rest_slot_count
    (r₀ jₓ k : ℕ) (b : Fin (jₓ+1)) (i : Fin r₀) :
    ((Finset.univ : Finset
        {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}).filter
      (fun z => z.val.1.val < k)).card ≤ k*r₀ := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let S := {z : I // z.val.1.val < k}
  let e : S → Fin k × Fin r₀ := fun z =>
    (⟨z.val.val.1.val, z.property⟩, z.val.val.2)
  have hinj : Function.Injective e := by
    intro x y h
    have h1 : x.val.val.1.val = y.val.val.1.val :=
      congrArg (fun a : Fin k × Fin r₀ => a.1.val) h
    have h2 : x.val.val.2 = y.val.val.2 :=
      congrArg (fun a : Fin k × Fin r₀ => a.2) h
    exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext h1) h2))
  have hCard : Fintype.card S ≤ Fintype.card (Fin k × Fin r₀) :=
    Fintype.card_le_of_injective e hinj
  simpa [S, I, Fintype.card_subtype, Fintype.card_prod] using hCard



/- Exact source owner: SourceOriginalQUniformMacroFactor.lean; original line 37. -/
theorem source_original_Q_scaled_midpoint_ratio
    (ε s : ℝ) (hεsmall : ε ≤ 1/10) (hs : s ≠ 0) :
    ((11/10+ε)*s)/((11/10-ε)*s) =
      (11/10+ε)/(11/10-ε) := by
  have hden : (11/10-ε:ℝ) ≠ 0 := by linarith
  field_simp

/- The actual source rest-slot fractions are uniform on the first
k fixed macro bands and one on all unrestricted micro bands. -/



/- Exact source owner: SourceOriginalQUniformMacroFactor.lean; original line 46. -/
theorem source_original_Q_joint_gamma_eq_uniform
    (r₀ jₓ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hεsmall : ε ≤ 1/10)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) :
    sourceOriginalQJointRestGamma r₀ jₓ k ε b i z =
      if z.val.1.val < k then sourceOriginalQUniformGamma ε else 1 := by
  by_cases hj : z.val.1.val < k
  · let s := sourceOriginalQActualExponent r₀ z.val.1.val
    have hr : (0:ℝ) < r₀ := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
    have hs : 0 < s := by
      dsimp [s, sourceOriginalQActualExponent,sourceOriginalQ0Scale]
      positivity
    have hRatio := source_original_Q_scaled_midpoint_ratio
      ε s hεsmall (ne_of_gt hs)
    unfold sourceOriginalQJointRestGamma sourceOriginalQUniformGamma
    rw [if_pos hj, if_pos hj]
    dsimp only [s] at hRatio
    rw [hRatio]
  · simp [sourceOriginalQJointRestGamma,hj]



/- Exact source owner: SourceOriginalQUniformMacroFactor.lean; original line 12. -/
theorem source_original_Q_uniform_gamma_positive_le_one
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    0 < sourceOriginalQUniformGamma ε ∧
      sourceOriginalQUniformGamma ε ≤ 1 := by
  let a : ℝ := 11/10-ε
  let b : ℝ := 11/10+ε
  let z : ℝ := b/a
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hz : 0 < z := div_pos hb ha
  have hgt : 1 < z := (lt_div_iff₀ ha).mpr (by dsimp [a,b]; nlinarith)
  have hupper : z ≤ (6/5:ℝ) := by
    apply (div_le_iff₀ ha).mpr
    dsimp [a,b]
    nlinarith
  have hlogpos : 0 < Real.log z := Real.log_pos hgt
  have hlogupper : Real.log z ≤ z - 1 :=
    Real.log_le_sub_one_of_pos hz
  change 0 < Real.log z /16 ∧ Real.log z /16 ≤ 1
  constructor
  · linarith
  · linarith

/- The source dyadic midpoint ratio cancels its actual band scale.
Consequently every fixed-index macro slot has the SAME fraction. -/



/- Exact source owner: SourceOriginalQUniformJointFloor.lean; original line 9. -/
theorem source_original_Q_joint_gamma_uniform_floor
    (r₀ jₓ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10)
    (b : Fin (jₓ+1)) (i : Fin r₀) :
    (sourceOriginalQUniformGamma ε)^(k*r₀) ≤
      ∏ z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)},
        sourceOriginalQJointRestGamma r₀ jₓ k ε b i z := by
  classical
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let g := sourceOriginalQUniformGamma ε
  let A : Finset I := Finset.univ.filter (fun z => z.val.1.val < k)
  have hg : 0 < g ∧ g ≤ 1 :=
    source_original_Q_uniform_gamma_positive_le_one ε hε hεsmall
  have hProd : (∏ z : I, sourceOriginalQJointRestGamma
      r₀ jₓ k ε b i z) = g^A.card := by
    calc
      _ = ∏ z : I, (if z.val.1.val < k then g else 1) := by
        apply Finset.prod_congr rfl
        intro z hz
        exact source_original_Q_joint_gamma_eq_uniform
          r₀ jₓ k hr₀ ε hεsmall b i z
      _ = ∏ z ∈ A, g := by
        rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, mul_one]
        rfl
      _ = g ^ A.card := by simp
  have hCount : A.card ≤ k*r₀ :=
    source_original_Q_fixed_macro_rest_slot_count r₀ jₓ k b i
  have hPow : g^(k*r₀) ≤ g^A.card :=
    pow_le_pow_of_le_one hg.1.le hg.2 hCount
  simpa only [g] using hPow.trans_eq hProd.symm



/- Exact source owner: SourceOriginalQRestrictedMidpointPNT.lean; original line 35. -/
theorem source_original_Q_restricted_midpoint_mass_eventually
    (r₀ j : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    let s := sourceOriginalQActualExponent r₀ j
    let u := (11/10-ε)*s
    let v := (11/10+ε)*s
    let ν := Real.log (v/u)/4
    0 < ν ∧
      (∀ᶠ L : ℝ in atTop,
        ν ≤ ∑ p ∈ sourceOriginalQRestrictedMidpoint r₀ j ε L,
          (p:ℝ)⁻¹) := by
  let s := sourceOriginalQActualExponent r₀ j
  let u := (11/10-ε)*s
  let v := (11/10+ε)*s
  let ν := Real.log (v/u)/4
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 < s := by
    dsimp [s,sourceOriginalQActualExponent,sourceOriginalQ0Scale]
    positivity
  have hu : s ≤ u := by dsimp [u]; nlinarith
  have hv : v ≤ (6/5:ℝ)*s := by dsimp [v]; nlinarith
  have huv : u < v := by dsimp [u,v]; nlinarith [mul_pos hε hs]
  have huPos : 0 < u := lt_of_lt_of_le hs hu
  have hratio : (1:ℝ) < v/u :=
    (lt_div_iff₀ huPos).mpr (by nlinarith [huv])
  have hν : 0 < ν := by
    dsimp [ν]
    have hh := Real.log_pos hratio
    linarith
  have hlog : 2*ν ≤ Real.log (v/u) := by
    dsimp [ν]
    linarith [Real.log_pos hratio]
  refine ⟨hν, ?_⟩
  have hh := source_prime_log_band_short_fixed_floor
    s ((6/5:ℝ)*s) u v ν hs hu (le_of_lt huv) hv hν hlog
  simpa only [sourceOriginalQRestrictedMidpoint, s, u, v]
    using hh



/- Exact source owner: SourceShiftTwoClosedMacroBands.lean; original line 15. -/
theorem source_prime_log_band_subset_closed
    (L u v : ℝ) :
    sourcePrimeLogBand L u v ⊆ sourceClosedPrimeLogBand L u v := by
  intro p hp
  have hPrime := (Finset.mem_filter.mp hp).2
  have hRange := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hf := Nat.lt_floor_add_one (Real.exp (u*L))
  have hNat : ((⌊Real.exp (u*L)⌋₊:ℕ):ℝ)+1 ≤ (p:ℝ) := by
    exact_mod_cast hRange.1
  have hLower : Real.exp (u*L) ≤ (p:ℝ) := by linarith
  have hCeil : ⌈Real.exp (u*L)⌉₊ ≤ p :=
    (Nat.ceil_le).2 hLower
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hCeil, hRange.2⟩, hPrime⟩

/- Source-closed dyadic bands inherit unconditional PNT2 floors
with correct endpoint convention. -/



/- Exact source owner: SourceOriginalQActualCenterPNT.lean; original line 11. -/
theorem source_original_Q_actual_subband_subset
    (r₀ jₓ : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (j : Fin (jₓ+1)) (u v : ℝ)
    (hLo : sourceOriginalQActualExponent r₀ j.val ≤ u)
    (hHi : v ≤ (6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val) :
    sourcePrimeLogBand L u v ⊆ sourceOriginalQActualBands r₀ jₓ L j := by
  intro p hp
  have hContained := source_prime_log_band_subset_closed L u v hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hContained).2
  have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hContained).1
  have hBottom : Real.exp (sourceOriginalQActualExponent r₀ j.val * L) ≤
      Real.exp (u*L) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hLo hL)
  have hTop : Real.exp (v*L) ≤
      Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHi hL)
  have hCeil : ⌈Real.exp (sourceOriginalQActualExponent r₀ j.val * L)⌉₊ ≤
      ⌈Real.exp (u*L)⌉₊ := Nat.ceil_le_ceil hBottom
  have hFloor : ⌊Real.exp (v*L)⌋₊ ≤
      ⌊Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)*L)⌋₊ :=
    Nat.floor_le_floor hTop
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hCeil.trans hpRange.1,
        hpRange.2.trans hFloor⟩,hpPrime⟩

/- Uniform (eventual) PNT lower mass of a STRICT interior
subband of any fixed original Q_j. The band is not enlarged or
replaced by an auxiliary distribution. -/



/- Exact source owner: SourceOriginalQRestrictedMidpointPNT.lean; original line 15. -/
theorem source_original_Q_restricted_midpoint_subset
    (r₀ jₓ : ℕ) (L ε : ℝ) (j : Fin (jₓ+1))
    (hr₀ : 1 ≤ r₀) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/10) :
    sourceOriginalQRestrictedMidpoint r₀ j.val ε L ⊆
      sourceOriginalQActualBands r₀ jₓ L j := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 < sourceOriginalQActualExponent r₀ j.val := by
    unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    positivity
  apply source_original_Q_actual_subband_subset r₀ jₓ L hL j
    ((11/10-ε)*sourceOriginalQActualExponent r₀ j.val)
    ((11/10+ε)*sourceOriginalQActualExponent r₀ j.val)
  · nlinarith
  · nlinarith

/- The reciprocal-prime mass of the RESTRICTED midpoint interval
is bounded below by a fixed positive number for each fixed j.
This is stronger than the existing whole-Q_j-band floor. -/



/- Exact source owner: SourceOriginalQMidpointLocalFraction.lean; original line 10. -/
theorem source_original_Q_subwindow_subtype_mass
    (Q A : Finset ℕ) (hA : A ⊆ Q) :
    (∑ p : {p // p ∈ Q},
      if p.val ∈ A then (p.val:ℝ)⁻¹ else 0) =
      ∑ p ∈ A, (p:ℝ)⁻¹ := by
  classical
  have hQ : (∑ p : {p // p ∈ Q},
      if p.val ∈ A then (p.val:ℝ)⁻¹ else 0) =
      ∑ p ∈ Q, if p ∈ A then (p:ℝ)⁻¹ else 0 :=
    Finset.sum_coe_sort Q (fun p : ℕ =>
      if p ∈ A then (p:ℝ)⁻¹ else 0)
  rw [hQ, ← Finset.sum_filter]
  have hEq : Q.filter (fun p => p ∈ A) = A := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨hA hp, hp⟩
  rw [hEq]

/- A fixed interior source Q_j midpoint receives a definite
fraction of the FULL genuine Q_j harmonic mass, uniformly for every
dyadic cutoff j_x containing that fixed index. -/



/- Exact source owner: SourceOriginalQMidpointLocalFraction.lean; original line 34. -/
theorem source_original_Q_midpoint_local_fraction_eventually
    (r₀ j : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    let s := sourceOriginalQActualExponent r₀ j
    let u := (11/10-ε)*s
    let v := (11/10+ε)*s
    let ν := Real.log (v/u)/4
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hj : j ≤ jₓ),
      (ν/4) *
        (∑ p ∈ sourceOriginalQActualBands r₀ jₓ L
          (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (jₓ+1)), (p:ℝ)⁻¹) ≤
        ∑ p : {p // p ∈ sourceOriginalQActualBands r₀ jₓ L
          (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (jₓ+1))},
          if p.val ∈ sourceOriginalQRestrictedMidpoint r₀ j ε L
          then (p.val:ℝ)⁻¹ else 0 := by
  let s := sourceOriginalQActualExponent r₀ j
  let u := (11/10-ε)*s
  let v := (11/10+ε)*s
  let ν := Real.log (v/u)/4
  have hData := source_original_Q_restricted_midpoint_mass_eventually
    r₀ j hr₀ ε hε hεsmall
  have hν : 0 < ν := hData.1
  have hMass : ∀ᶠ L : ℝ in atTop,
      ν ≤ ∑ p ∈ sourceOriginalQRestrictedMidpoint r₀ j ε L,
        (p:ℝ)⁻¹ := hData.2
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hs : 0 < s := by
    dsimp [s, sourceOriginalQActualExponent,sourceOriginalQ0Scale]
    positivity
  have hEnd : ∀ᶠ L : ℝ in atTop, 2 ≤ s*L := by
    filter_upwards [eventually_ge_atTop (2/s)] with L hL
    have hh := mul_le_mul_of_nonneg_left hL hs.le
    have hdiv : (2/s)*s = 2 := by field_simp
    nlinarith
  filter_upwards [hMass, hEnd, eventually_ge_atTop (0:ℝ)]
    with L hm ht hL
  intro jₓ hj
  let jj : Fin (jₓ+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  have hCap := source_original_Q_actual_band_harmonic_le_four
    r₀ jₓ L hr₀ jj ht
  have hSubset := source_original_Q_restricted_midpoint_subset
    r₀ jₓ L ε jj hr₀ hL hε.le hεsmall
  have hEq := source_original_Q_subwindow_subtype_mass
    (sourceOriginalQActualBands r₀ jₓ L jj)
    (sourceOriginalQRestrictedMidpoint r₀ j ε L) hSubset
  have hγ : 0 ≤ ν/4 := by positivity
  calc
    (ν/4) * (∑ p ∈ sourceOriginalQActualBands r₀ jₓ L jj,
          (p:ℝ)⁻¹) ≤ (ν/4)*4 :=
      mul_le_mul_of_nonneg_left hCap hγ
    _ = ν := by ring
    _ ≤ ∑ p ∈ sourceOriginalQRestrictedMidpoint r₀ j ε L,
          (p:ℝ)⁻¹ := hm
    _ = _ := hEq.symm



/- Exact source owner: SourceOriginalQRestMaskProduct.lean; original line 10. -/
theorem source_original_Q_restricted_rest_mass_product
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (Good : (k : {k : B × Fin r // k ≠ (b,i)}) → Finset ℕ) :
    (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1},
      if (∀ k, (rest k).val ∈ Good k) then
        (∏ _b : B, (r.factorial:ℝ)⁻¹) /
          (((∏ k : {k : B × Fin r // k ≠ (b,i)},
            (rest k).val):ℕ):ℝ)
      else 0) =
    (∏ _b : B, (r.factorial:ℝ)⁻¹) *
      (∏ k : {k : B × Fin r // k ≠ (b,i)},
        ∑ p : {p // p ∈ Q k.1.1},
          if p.val ∈ Good k then (p.val:ℝ)⁻¹ else 0) := by
  classical
  let I := {k : B × Fin r // k ≠ (b,i)}
  let C : ℝ := ∏ _b : B, (r.factorial:ℝ)⁻¹
  let F (k : I) (p : {p // p ∈ Q k.1.1}) : ℝ :=
    if p.val ∈ Good k then (p.val:ℝ)⁻¹ else 0
  have hPoint (rest : (k : I) → {p // p ∈ Q k.1.1}) :
      (if (∀ k, (rest k).val ∈ Good k) then
        C / (((∏ k : I, (rest k).val):ℕ):ℝ) else 0) =
        C * ∏ k : I, F k (rest k) := by
    by_cases hg : ∀ k, (rest k).val ∈ Good k
    · rw [if_pos hg]
      have hF : ∀ k : I, F k (rest k) = ((rest k).val:ℝ)⁻¹ := by
        intro k
        simp [F,hg k]
      simp_rw [hF]
      rw [Finset.prod_inv_distrib]
      norm_cast
    · rw [if_neg hg]
      obtain ⟨k,hk⟩ := not_forall.mp hg
      have hZero : F k (rest k) = 0 := by simp [F,hk]
      have hProd : (∏ j : I, F j (rest j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hZero
      rw [hProd]
      ring
  calc
    _ = ∑ rest : (k : I) → {p // p ∈ Q k.1.1},
        C * (∏ k : I, F k (rest k)) := by
          apply Finset.sum_congr rfl
          intro rest hrest
          exact hPoint rest
    _ = C * (∑ rest : (k : I) → {p // p ∈ Q k.1.1},
        ∏ k : I, F k (rest k)) := by rw [Finset.mul_sum]
    _ = C * (∏ k : I,
        ∑ p : {p // p ∈ Q k.1.1}, F k p) := by
          congr 1
          have h := Finset.prod_univ_sum
            (fun k : I => (Finset.univ : Finset {p // p ∈ Q k.1.1}))
            F
          rw [Fintype.piFinset_univ] at h
          exact h.symm
    _ = _ := rfl



/- Exact source owner: SourceOriginalQRestFraction.lean; original line 10. -/
theorem source_original_Q_restricted_rest_fraction_lower
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (Good : (k : {k : B × Fin r // k ≠ (b,i)}) → Finset ℕ)
    (γ : {k : B × Fin r // k ≠ (b,i)} → ℝ)
    (hγ : ∀ k, 0 ≤ γ k)
    (hLocal : ∀ k : {k : B × Fin r // k ≠ (b,i)},
      γ k * (∑ p ∈ Q k.val.1, (p:ℝ)⁻¹) ≤
        ∑ p : {p // p ∈ Q k.val.1},
          if p.val ∈ Good k then (p.val:ℝ)⁻¹ else 0) :
    (∏ k : {k : B × Fin r // k ≠ (b,i)}, γ k) *
      (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
         {p // p ∈ Q k.1.1},
        (∏ _b : B, (r.factorial:ℝ)⁻¹) /
          (((∏ k : {k : B × Fin r // k ≠ (b,i)},
            (rest k).val):ℕ):ℝ)) ≤
      (∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
         {p // p ∈ Q k.1.1},
        if (∀ k, (rest k).val ∈ Good k) then
          (∏ _b : B, (r.factorial:ℝ)⁻¹) /
            (((∏ k : {k : B × Fin r // k ≠ (b,i)},
              (rest k).val):ℕ):ℝ)
        else 0) := by
  classical
  let I := {k : B × Fin r // k ≠ (b,i)}
  let C : ℝ := ∏ _b : B, (r.factorial:ℝ)⁻¹
  let V (k : I) : ℝ := ∑ p ∈ Q k.val.1, (p:ℝ)⁻¹
  let W (k : I) : ℝ :=
    ∑ p : {p // p ∈ Q k.val.1},
      if p.val ∈ Good k then (p.val:ℝ)⁻¹ else 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hV (k : I) : 0 ≤ V k := by dsimp [V]; positivity
  have hTermNonneg (k : I) : 0 ≤ γ k * V k :=
    mul_nonneg (hγ k) (hV k)
  have hProd :
      (∏ k : I, γ k * V k) ≤ (∏ k : I, W k) := by
    apply Finset.prod_le_prod₀
    · intro k hk
      exact hTermNonneg k
    · intro k hk
      exact hLocal k
  have hProd' : (∏ k : I, γ k) * (∏ k : I, V k) ≤
      (∏ k : I, W k) := by
    rw [← Finset.prod_mul_distrib]
    exact hProd
  have hRest := source_original_Q_rest_harmonic_mass_exact r Q b i
  have hMask := source_original_Q_restricted_rest_mass_product
    r Q b i Good
  calc
    _ = (∏ k : I, γ k) * (C * (∏ k : I, V k)) := by
          rw [hRest]
    _ = C * ((∏ k : I, γ k) * (∏ k : I, V k)) := by ring
    _ ≤ C * (∏ k : I, W k) :=
      mul_le_mul_of_nonneg_left hProd' hC
    _ = _ := by
      rw [← hMask]



/- Exact source owner: SourceOriginalQJointMidpoint.lean; original line 35. -/
theorem source_original_Q_joint_rest_fraction_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (jₓ : ℕ) (b : Fin (jₓ+1)) (i : Fin r₀),
      let Q := sourceOriginalQActualBands r₀ jₓ L
      let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
      let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
      let γ := sourceOriginalQJointRestGamma r₀ jₓ k ε b i
      (∏ z : I, γ z) *
        (∑ rest : (z : I) → {p // p ∈ Q z.val.1},
          (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z : I, (rest z).val):ℕ):ℝ)) ≤
        (∑ rest : (z : I) → {p // p ∈ Q z.val.1},
          if (∀ z, (rest z).val ∈ Good z) then
            (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
              (((∏ z : I, (rest z).val):ℕ):ℝ)
          else 0) := by
  have hUniform := Filter.eventually_all.2
    (fun j : Fin k => source_original_Q_midpoint_local_fraction_eventually
      r₀ j.val hr₀ ε hε hεsmall)
  filter_upwards [hUniform, eventually_ge_atTop (0:ℝ)]
    with L hMid hL
  intro jₓ b i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
  let γ := sourceOriginalQJointRestGamma r₀ jₓ k ε b i
  have hγ (z : I) : 0 ≤ γ z := by
    by_cases hj : z.val.1.val < k
    · have hh := (source_original_Q_restricted_midpoint_mass_eventually
        r₀ z.val.1.val hr₀ ε hε hεsmall).1
      dsimp [γ,sourceOriginalQJointRestGamma]
      rw [if_pos hj]
      dsimp at hh
      linarith
    · simp [γ,sourceOriginalQJointRestGamma,hj]
  have hLocal (z : I) :
      γ z * (∑ p ∈ Q z.val.1, (p:ℝ)⁻¹) ≤
        ∑ p : {p // p ∈ Q z.val.1},
          if p.val ∈ Good z then (p.val:ℝ)⁻¹ else 0 := by
    by_cases hj : z.val.1.val < k
    · let jj : Fin k := ⟨z.val.1.val,hj⟩
      have hjBound : jj.val ≤ jₓ :=
        Nat.lt_succ_iff.mp z.val.1.isLt
      have hh := hMid jj jₓ hjBound
      have hEq : (⟨jj.val,Nat.lt_succ_of_le hjBound⟩ : Fin (jₓ+1)) =
          z.val.1 := Fin.ext rfl
      dsimp [γ,Good,sourceOriginalQJointRestGamma,
        sourceOriginalQJointRestAllowed]
      simp only [if_pos hj]
      have hDiv (t : ℝ) : t/4/4 = t/16 := by ring
      rw [hDiv] at hh
      rw [← Finset.univ_eq_attach
        (sourceOriginalQActualBands r₀ jₓ L z.val.1)]
      simpa only [jj,hEq,Q] using hh
    · have hEq : Good z = Q z.val.1 := by
        dsimp [Good,sourceOriginalQJointRestAllowed]
        rw [if_neg hj]
      have hγ1 : γ z = 1 := by
        simp [γ,sourceOriginalQJointRestGamma,hj]
      rw [hEq,hγ1,one_mul]
      have hh := Finset.sum_coe_sort (Q z.val.1) (fun p : ℕ => (p:ℝ)⁻¹)
      have hMask :
          (∑ p : {p // p ∈ Q z.val.1},
            if p.val ∈ Q z.val.1 then (p.val:ℝ)⁻¹ else 0) =
          (∑ p ∈ Q z.val.1, (p:ℝ)⁻¹) := by
            simpa using hh
      exact le_of_eq hMask.symm
  exact source_original_Q_restricted_rest_fraction_lower
    r₀ Q b i Good γ hγ hLocal



/- Exact source owner: SourceOriginalQJointPositiveRest.lean; original line 36. -/
theorem source_original_Q_actual_positive_good_rest_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    0 < (sourceOriginalQUniformGamma ε)^(k*r₀) ∧
    (∀ᶠ L : ℝ in atTop,
      ∀ (jₓ : ℕ) (b : Fin (jₓ+1)) (i : Fin r₀),
        (sourceOriginalQUniformGamma ε)^(k*r₀) *
          sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i ≤
          sourceOriginalQActualGoodRestHarmonicMass
            r₀ jₓ k L ε b i) := by
  have hG : 0 < sourceOriginalQUniformGamma ε :=
    (source_original_Q_uniform_gamma_positive_le_one ε hε hεsmall).1
  constructor
  · positivity
  have hh := source_original_Q_joint_rest_fraction_eventually
    r₀ k hr₀ ε hε hεsmall
  filter_upwards [hh] with L hJoint
  intro jₓ b i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  have hNN : 0 ≤ sourceOriginalQActualRestHarmonicMass
      r₀ jₓ L b i := by
    unfold sourceOriginalQActualRestHarmonicMass
    apply Finset.sum_nonneg
    intro rest hrest
    positivity
  have hProd := source_original_Q_joint_gamma_uniform_floor
    r₀ jₓ k hr₀ ε hε hεsmall b i
  have hJoint' := hJoint jₓ b i
  change
    (∏ z : I, sourceOriginalQJointRestGamma r₀ jₓ k ε b i z) *
      sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i ≤
        sourceOriginalQActualGoodRestHarmonicMass
          r₀ jₓ k L ε b i at hJoint'
  calc
    (sourceOriginalQUniformGamma ε)^(k*r₀) *
        sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i ≤
      (∏ z : I, sourceOriginalQJointRestGamma r₀ jₓ k ε b i z) *
        sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i :=
      mul_le_mul_of_nonneg_right hProd hNN
    _ ≤ _ := hJoint'



/- Exact source owner: SourceOriginalQ0GoodRestNormalized.lean; original line 12. -/
theorem source_original_Q0_good_rest_full_labelled_HQ_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (i : Fin r₀),
      (sourceOriginalQUniformGamma ε)^(k*r₀) *
        (∑ f : (z : Fin (jₓ+1) × Fin r₀) →
          {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.1},
          (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z, (f z).val):ℕ):ℝ)) ≤
      4 * sourceOriginalQActualGoodRestHarmonicMass
        r₀ jₓ k L ε ⟨0,Nat.succ_pos jₓ⟩ i := by
  let s : ℝ := sourceOriginalQActualExponent r₀ 0
  have hs : 0 < s := by
    dsimp [s,sourceOriginalQActualExponent,sourceOriginalQ0Scale]
    have hr : (0:ℝ) < (r₀:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
    positivity
  have hσ : 0 < sourceOriginalQUniformGamma ε :=
    (source_original_Q_uniform_gamma_positive_le_one ε hε hεsmall).1
  have hGamma : 0 ≤ (sourceOriginalQUniformGamma ε)^(k*r₀) :=
    le_of_lt (pow_pos hσ _)
  have hAtTop : ∀ᶠ L : ℝ in atTop, 2 ≤ s*L := by
    filter_upwards [eventually_ge_atTop (2/s)] with L hL
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hh := mul_le_mul_of_nonneg_left hL hs.le
    have heq : s*(2/s) = 2 := by field_simp
    nlinarith
  have hGood := (source_original_Q_actual_positive_good_rest_eventually
    r₀ k hr₀ ε hε hεsmall).2
  filter_upwards [hAtTop, hGood] with L ht hRestGood
  intro jₓ i
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let H := sourceOriginalQActualRestHarmonicMass r₀ jₓ L b i
  let W := sourceOriginalQActualGoodRestHarmonicMass r₀ jₓ k L ε b i
  have hCap := source_original_Q0_labelled_HQ_le_four_rest
    r₀ jₓ L hr₀ (by simpa only [s] using ht) i
  have hGoodL : (sourceOriginalQUniformGamma ε)^(k*r₀) * H ≤ W :=
    hRestGood jₓ b i
  calc
    _ ≤ (sourceOriginalQUniformGamma ε)^(k*r₀) * (4*H) :=
      mul_le_mul_of_nonneg_left hCap hGamma
    _ = 4*((sourceOriginalQUniformGamma ε)^(k*r₀)*H) := by ring
    _ ≤ 4*W := mul_le_mul_of_nonneg_left hGoodL (by norm_num)



/- Exact source owner: SourceOriginalQPGoodMassBound.lean; original line 38. -/
theorem source_original_QP_actual_good_mass_product_floor_eventually
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (i : Fin r₀),
      ((sourceOriginalQUniformGamma ε)^(k*r₀) *
        (sourceOriginalPGroupParityDelta/2)) *
      ((∑ f : (z : Fin (jₓ+1) × Fin r₀) →
          {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.1},
          (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z, (f z).val):ℕ):ℝ)) *
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      4 * sourceOriginalQActualGoodRestHarmonicMass
        r₀ jₓ k L ε ⟨0,Nat.succ_pos jₓ⟩ i *
        sourceOriginalPActualGoodHarmonicMass r₀ L := by
  have hQ := source_original_Q0_good_rest_full_labelled_HQ_eventually
    r₀ k hr₀ ε hε hεsmall
  have hP := source_original_P_good_harmonic_mass_floor_eventually r₀ hr₀
  have hLocal := source_original_P_all_actual_local_eventually r₀
  filter_upwards [hQ,hP,hLocal] with L hQL hPL hLocalL
  intro jₓ i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let A : ℝ := ∑ f : (z : Fin (jₓ+1) × Fin r₀) →
      {p // p ∈ Q z.1},
      (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
        (((∏ z, (f z).val):ℕ):ℝ)
  let QGood := sourceOriginalQActualGoodRestHarmonicMass
    r₀ jₓ k L ε b i
  let PGood := sourceOriginalPActualGoodHarmonicMass r₀ L
  let γ : ℝ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ : ℝ := sourceOriginalPGroupParityDelta/2
  have hQbound : γ*A ≤ 4*QGood := hQL jₓ i
  have hPbound : δ*sourceLiteralHP P ≤ PGood := hPL
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocalL.2.1 g p hp)
  have hHP : 1 ≤ sourceLiteralHP P :=
    source_literal_HP_one_le P h3 hLocalL.1
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos source_original_P_group_parity_delta_positive (by norm_num)
  have hδHP : 0 ≤ δ*sourceLiteralHP P :=
    mul_nonneg (le_of_lt hδpos) (by linarith)
  have hQGoodNN : 0 ≤ QGood := by
    dsimp [QGood, sourceOriginalQActualGoodRestHarmonicMass]
    apply Finset.sum_nonneg
    intro rest hrest
    split_ifs <;> positivity
  change (γ*δ)*(A*sourceLiteralHP P) ≤ 4*QGood*PGood
  calc
    (γ*δ)*(A*sourceLiteralHP P) =
        (γ*A)*(δ*sourceLiteralHP P) := by ring
    _ ≤ (4*QGood)*(δ*sourceLiteralHP P) :=
      mul_le_mul_of_nonneg_right hQbound hδHP
    _ ≤ (4*QGood)*PGood :=
      mul_le_mul_of_nonneg_left hPbound (by positivity)
    _ = 4*QGood*PGood := by ring



/- Exact source owner: SourceOriginalQPGoodRestriction.lean; original line 9. -/
noncomputable def sourceOriginalQPLiteralTerm
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
  (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
    sourceOriginalW1 P R.val *
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent
      (Finset.univ.biUnion P) R.val)/2) *
    Ψ (((((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) : ℕ) : ℝ) / x)

/- Every literal term is nonnegative under the source's
nonnegative cutoff, without changing multiplicity parity. -/



/- Exact source owner: SourceShiftTwoXACanonicalConditional.lean; original line 9. -/
def sourceOriginalQSlotsCurryEquiv
    {B : Type} (r : ℕ) (Q : B → Finset ℕ) :
    ((k : B × Fin r) → {p // p ∈ Q k.1}) ≃
    ((b : B) → Fin r → {p // p ∈ Q b}) where
  toFun f b i := f (b,i)
  invFun f k := f k.1 k.2
  left_inv f := by
    funext k
    cases k
    rfl
  right_inv f := by
    funext b i
    rfl

/- Exact pointwise sampling weight of the actual A(u)Psi(u/x),
with ALL r! denominators and the genuine source W1/parity. -/



/- Exact source owner: SourceOriginalQPRestPruning.lean; original line 10. -/
noncomputable def sourceOriginalQPActualFreeTerm
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
    then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0

/- The true conditional free-prime term is nonnegative for source Psi. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 104. -/
theorem source_original_parity_projection_zero_or_one
    (Pall : Finset ℕ) (u : ℕ) :
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent Pall u)/2)
      = 0 ∨
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent Pall u)/2)
      = 1 := by
  rcases neg_one_pow_eq_or ℝ (sourceOriginalPParityExponent Pall u)
    with h | h
  · left
    rw [h]
    ring
  · right
    rw [h]
    ring



/- Exact source owner: SourceOriginalQPGoodRestriction.lean; original line 23. -/
theorem source_original_QP_literal_term_nonneg
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) (hΨ : ∀ t, 0 ≤ Ψ t)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    0 ≤ sourceOriginalQPLiteralTerm r Q P x Ψ f R := by
  have hParity : 0 ≤
      (1 - (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2 := by
    rcases source_original_parity_projection_zero_or_one
      (Finset.univ.biUnion P) R.val with hh | hh
    · rw [hh]
    · rw [hh]
      norm_num
  unfold sourceOriginalQPLiteralTerm
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity)
      (source_original_W1_nonneg P R.val)) hParity) (hΨ _)
/- Any genuine Q×P good event gives a lower sub-sum for original X_A.
This is actual pruning of the exact full weighted disintegration,
not an assumed mass lower bound for the good event. -/



/- Exact source owner: SourceOriginalQPRestPruning.lean; original line 25. -/
theorem source_original_QP_actual_free_term_nonneg
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ t, 0 ≤ Ψ t)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1})
    (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
    0 ≤ sourceOriginalQPActualFreeTerm r Q P b i x Ψ rest R := by
  unfold sourceOriginalQPActualFreeTerm
  apply Finset.sum_nonneg
  intro p hp
  let f := (sourceOriginalQSlotsCurryEquiv r Q)
    ((Equiv.piSplitAt (b,i)
      (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest))
  change 0 ≤ (if (∏ j : B, ∏ m : Fin r, (f j m).val)*R.val < ⌊2*x⌋₊+1
    then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0)
  split_ifs with hc
  · exact source_original_QP_literal_term_nonneg r Q P x Ψ hΨ _ R
  · exact le_rfl

/- Even after summing the free Q-prime, the original u cutoff
forces finite support in the true positive P-supported variable. -/



/- Exact source owner: SourceOriginalQPBoundedSummable.lean; original line 9. -/
theorem source_original_P_bounded_finite
    (Pall : Finset ℕ) (N : ℕ) :
    ({R : sourceOriginalPSupported Pall | R.val < N} : Set
       (sourceOriginalPSupported Pall)).Finite := by
  have hPre : (Subtype.val ⁻¹' Set.Iio N : Set
      (sourceOriginalPSupported Pall)).Finite := by
    apply Set.Finite.preimage
      (fun x hx y hy h => Subtype.ext h)
    exact Set.finite_Iio N
  simpa [Set.preimage, Set.Iio] using hPre

/- Natural cutoff qR<N makes the genuine unrestricted P-supported
sum finite, independently of the weight used on that sum. -/



/- Exact source owner: SourceOriginalQPRestPruning.lean; original line 48. -/
theorem source_original_QP_actual_free_term_summable
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
      {p // p ∈ Q k.1.1}) :
    Summable (sourceOriginalQPActualFreeTerm r Q P b i x Ψ rest) := by
  let N : ℕ := ⌊2*x⌋₊+1
  apply summable_of_hasFiniteSupport
  apply (source_original_P_bounded_finite (Finset.univ.biUnion P) N).subset
  intro R hSupport
  by_contra hNot
  have hRbig : N ≤ R.val := Nat.le_of_not_gt hNot
  have hZero : sourceOriginalQPActualFreeTerm r Q P b i x Ψ rest R = 0 := by
    unfold sourceOriginalQPActualFreeTerm
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
      then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0) = 0
    simp [hOff]
  exact hSupport hZero

/- Original XA dominates every genuine rest×P good event, after the
free Q slot has been summed. No good-mass positivity is postulated. -/



/- Exact source owner: SourceOriginalQActualDisjoint.lean; original line 7. -/
theorem source_original_positive_dyadic_scale
    (r₀ j : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 < L) :
    0 < sourceOriginalPGroupScale r₀ L j := by
  have hr : (0:ℝ) < (r₀:ℝ) := by exact_mod_cast hr₀
  unfold sourceOriginalPGroupScale
  positivity

/- Every pair of genuine, closed, distinct original Q bands is
arithmetically disjoint, with no dropped endpoint primes. -/



/- Exact source owner: SourceOriginalQActualDisjoint.lean; original line 52. -/
theorem source_original_Q_actual_all_P_disjoint
    (r₀ jₓ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 < L) :
    ∀ (j : Fin (jₓ+1)) (g : sourceOriginalPAllGroupType r₀ L)
      (p : ℕ),
      p ∈ sourceOriginalQActualBands r₀ jₓ L j →
      p ∈ sourceOriginalPAllActualBands r₀ L g → False := by
  intro j g p hpQ hpP
  let a : ℝ := sourceOriginalPGroupScale r₀ L j.val
  let b : ℝ := sourceOriginalPGroupScale r₀ L g.val
  have ha : 0 < a := source_original_positive_dyadic_scale r₀ j.val L hr₀ hL
  have hb : 0 < b := source_original_positive_dyadic_scale r₀ g.val L hr₀ hL
  have hQ := source_original_Q_actual_prime_range r₀ jₓ L hr₀ j p hpQ
  have hP := source_original_P_closed_range ((3/2:ℝ)*b) p hpP
  by_cases hlt : j.val < g.val
  · have hSep := source_original_P_actual_scale_dyadic_separation
      r₀ j.val g.val L hr₀ hL hlt
    have hGap : (6/5:ℝ)*((3/2:ℝ)*b) < a := by
      dsimp [a,b] at *
      nlinarith
    have he := Real.exp_strictMono hGap
    linarith
  · by_cases hgt : g.val < j.val
    · have hSep := source_original_P_actual_scale_dyadic_separation
        r₀ g.val j.val L hr₀ hL hgt
      have hGap : (6/5:ℝ)*a < (3/2:ℝ)*b := by
        dsimp [a,b] at *
        nlinarith
      have he := Real.exp_strictMono hGap
      linarith
    · have heq : j.val = g.val := by omega
      have hGap : (6/5:ℝ)*a < (3/2:ℝ)*b := by
        dsimp [a,b] at *
        rw [← heq]
        nlinarith
      have he := Real.exp_strictMono hGap
      linarith



/- Exact source owner: SourceOriginalQActualDisjoint.lean; original line 16. -/
theorem source_original_Q_actual_all_disjoint
    (r₀ jₓ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 < L) :
    ∀ j k : Fin (jₓ+1), ∀ p,
      p ∈ sourceOriginalQActualBands r₀ jₓ L j →
      p ∈ sourceOriginalQActualBands r₀ jₓ L k → j = k := by
  intro j k p hpj hpk
  by_contra hNe
  have hval : j.val ≠ k.val := by
    intro hh
    exact hNe (Fin.ext hh)
  obtain hjk | hkj := lt_or_gt_of_ne hval
  · have hSep := source_original_P_actual_scale_dyadic_separation
      r₀ j.val k.val L hr₀ hL hjk
    have hPos := source_original_positive_dyadic_scale r₀ k.val L hr₀ hL
    have hGap : (6/5:ℝ)*sourceOriginalPGroupScale r₀ L k.val <
        sourceOriginalPGroupScale r₀ L j.val := by nlinarith
    have hjRange := source_original_Q_actual_prime_range
      r₀ jₓ L hr₀ j p hpj
    have hkRange := source_original_Q_actual_prime_range
      r₀ jₓ L hr₀ k p hpk
    have he := Real.exp_strictMono hGap
    linarith
  · have hSep := source_original_P_actual_scale_dyadic_separation
      r₀ k.val j.val L hr₀ hL hkj
    have hPos := source_original_positive_dyadic_scale r₀ j.val L hr₀ hL
    have hGap : (6/5:ℝ)*sourceOriginalPGroupScale r₀ L j.val <
        sourceOriginalPGroupScale r₀ L k.val := by nlinarith
    have hjRange := source_original_Q_actual_prime_range
      r₀ jₓ L hr₀ j p hpj
    have hkRange := source_original_Q_actual_prime_range
      r₀ jₓ L hr₀ k p hpk
    have he := Real.exp_strictMono hGap
    linarith

/- The complete ORIGINAL dyadic Q family and complete P group
family are disjoint, including equality of dyadic indices. -/



/- Exact source owner: SourceOriginalQPFiniteFubini.lean; original line 10. -/
theorem source_original_QP_finite_prime_P_tsum_comm
    {I : Type} [Fintype I]
    (Pall : Finset ℕ) (N : ℕ)
    (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (F : I → sourceOriginalPSupported Pall → ℝ) :
    (∑ i : I, ∑' R : sourceOriginalPSupported Pall,
      if q i * R.val < N then F i R else 0) =
    ∑' R : sourceOriginalPSupported Pall,
      ∑ i : I, if q i * R.val < N then F i R else 0 := by
  classical
  let f : I → sourceOriginalPSupported Pall → ℝ :=
    fun i R => if q i * R.val < N then F i R else 0
  have hFin : (Set.univ ×ˢ
      {R : sourceOriginalPSupported Pall | R.val < N} :
      Set (I × sourceOriginalPSupported Pall)).Finite :=
    (Set.finite_univ).prod (source_original_P_bounded_finite Pall N)
  have hSub : Function.support (Function.uncurry f) ⊆
      Set.univ ×ˢ {R : sourceOriginalPSupported Pall | R.val < N} := by
    intro ⟨i,R⟩ hh
    rw [Set.mem_prod]
    constructor
    · exact Set.mem_univ i
    · change R.val < N
      by_contra hNot
      have hge : N ≤ R.val := Nat.le_of_not_gt hNot
      have hmul : R.val ≤ q i * R.val :=
        Nat.le_mul_of_pos_left R.val (hq i)
      have hOff : ¬ q i * R.val < N := Nat.not_lt.mpr (hge.trans hmul)
      apply hh
      simp [Function.uncurry, f, hOff]
  have hs : Summable (Function.uncurry f) :=
    summable_of_hasFiniteSupport (hFin.subset hSub)
  have hCom := Summable.tsum_comm (f:=f) hs
  simpa only [f, tsum_fintype] using hCom.symm



/- Exact source owner: SourceShiftTwoXAFreeSlotFinite.lean; original line 10. -/
theorem source_full_Q_one_free_slot_sum
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r)
    (F : ((k : B × Fin r) → {p // p ∈ Q k.1}) → ℝ) :
    (∑ f : (k : B × Fin r) → {p // p ∈ Q k.1}, F f) =
      ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        ∑ p : {p // p ∈ Q b},
          F ((Equiv.piSplitAt (b,i)
            (fun k : B × Fin r => {p // p ∈ Q k.1})).symm (p,rest)) := by
  classical
  let e := Equiv.piSplitAt (b,i)
    (fun k : B × Fin r => {p // p ∈ Q k.1})
  change (∑ f, F f) = ∑ rest, ∑ p, F (e.symm (p,rest))
  calc
    (∑ f, F f) =
      ∑ pair : {p // p ∈ Q b} ×
          ((k : {k : B × Fin r // k ≠ (b,i)}) →
            {p // p ∈ Q k.1.1}), F (e.symm pair) :=
              (Equiv.sum_comp e.symm F).symm
    _ = ∑ p : {p // p ∈ Q b}, ∑ rest,
          F (e.symm (p,rest)) := Fintype.sum_prod_type _
    _ = ∑ rest, ∑ p : {p // p ∈ Q b},
          F (e.symm (p,rest)) := Finset.sum_comm
/- Source harmonic sampling term at a fixed P-prime-power integer R.
The numerator U is retained to match X_A's physical coefficient;
W1 uses distinct omega, while parity uses exponent multiplicities.
All Q-slot factorials and the original cutoff remain present. -/



/- Exact source owner: SourceShiftTwoXACanonicalConditional.lean; original line 25. -/
noncomputable def sourceOriginalQSamplingWeight
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (P : G → Finset ℕ) (u : ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
    sourceOriginalW1 P u *
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent
       (Finset.univ.biUnion P) u)/2) * Ψ ((u:ℝ)/x)
/- This conditions the LITERAL source X_A on one labelled Q slot,
not an auxiliary normalized law. The orbit membership is left
explicit rather than silently assuming completeness of a fiber. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 136. -/
theorem source_original_ordinary_times_P_part
    (Pall : Finset ℕ) (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalOrdinaryPart Pall u *
      sourceOriginalPPrimePart Pall u = u := by
  unfold sourceOriginalOrdinaryPart sourceOriginalPPrimePart
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter u.primeFactors Pall)]
  rw [Finset.sdiff_union_inter]
  exact (Nat.prod_primeFactors_pow_factorization hu).symm



/- Exact source owner: SourcePPrimePowerOrdinary.lean; original line 10. -/
theorem source_original_P_supported_iff_ordinary_one
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalOrdinaryPart P u = 1 ↔
      u.primeFactors ⊆ P := by
  constructor
  · intro hOrd
    have hSplit := source_original_ordinary_times_P_part P u hu
    rw [hOrd, one_mul] at hSplit
    have hVec := source_original_P_prime_part_eq_vector_product
      P hPrime u hu
    have hSupp := source_original_P_power_primeFactors_subset
      P hPrime (sourceOriginalPExponentVector P u)
    have hEq : u =
        sourceOriginalPPrimePowerProduct P
          (sourceOriginalPExponentVector P u) := hSplit.symm.trans hVec
    rw [hEq]
    exact hSupp
  · intro hSupp
    unfold sourceOriginalOrdinaryPart
    have hEmpty : u.primeFactors \ P = ∅ := by
      ext p
      constructor
      · intro hp
        have hParts := Finset.mem_sdiff.mp hp
        exact False.elim (hParts.2 (hSupp hParts.1))
      · intro hp
        simp at hp
    simp [hEmpty]

/- Literal source W1-harmonic unnormalized sum on positive
P-supported n, without changing the weight function. -/


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Mass007 -/

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


/- Exact source owner: SourceOriginalQPOrdinaryFibre.lean; original line 11. -/
theorem source_original_QP_ordinary_part_product
    (Pall : Finset ℕ) (q : ℕ)
    (R : sourceOriginalPSupported Pall)
    (hq : q ≠ 0)
    (hPrime : ∀ p ∈ Pall, p.Prime)
    (hNoP : ∀ p ∈ Pall, ¬p ∣ q) :
    sourceOriginalOrdinaryPart Pall (q*R.val) = q := by
  have hR : R.val ≠ 0 := R.property.1
  have hRpart : sourceOriginalPPrimePart Pall R.val = R.val := by
    have hOrd : sourceOriginalOrdinaryPart Pall R.val = 1 :=
      (source_original_P_supported_iff_ordinary_one
        Pall hPrime R.val hR).2 R.property.2
    have hh := source_original_ordinary_times_P_part Pall R.val hR
    rw [hOrd, one_mul] at hh
    exact hh
  have hExpo : sourceOriginalPExponentVector Pall (q*R.val) =
      sourceOriginalPExponentVector Pall R.val := by
    funext z
    dsimp [sourceOriginalPExponentVector]
    rw [Nat.factorization_mul hq hR]
    simp only [Finsupp.add_apply]
    have hz : q.factorization z.val = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (hNoP z.val z.property)
    simp [hz]
  have hPart : sourceOriginalPPrimePart Pall (q*R.val) =
      sourceOriginalPPrimePart Pall R.val := by
    rw [source_original_P_prime_part_eq_vector_product
        Pall hPrime (q*R.val) (mul_ne_zero hq hR),
      source_original_P_prime_part_eq_vector_product
        Pall hPrime R.val hR, hExpo]
  have hSplit := source_original_ordinary_times_P_part
    Pall (q*R.val) (mul_ne_zero hq hR)
  rw [hPart, hRpart] at hSplit
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR) hSplit



/- Exact source owner: SourceOriginalQPWeightedSupport.lean; original line 48. -/
theorem source_original_P_multiplicity_nonP_mul
    (Pall : Finset ℕ) (q R : ℕ)
    (hq : q ≠ 0) (hR : R ≠ 0)
    (hNoP : ∀ p ∈ Pall, ¬p ∣ q) :
    sourceOriginalPParityExponent Pall (q*R) =
      sourceOriginalPParityExponent Pall R := by
  unfold sourceOriginalPParityExponent
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.factorization_mul hq hR]
  simp only [Finsupp.add_apply]
  have hqZero : q.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (hNoP p hp)
  simp [hqZero]

/- The exact multiplicity parity projection of sourceOriginalA is
unchanged under addition of ordinary Q-slots free of all P-primes. -/



/- Exact source owner: SourceOriginalQPWeightedSupport.lean; original line 10. -/
theorem source_original_group_omega_nonP_mul
    (P : Finset ℕ) (q R : ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hNoP : ∀ p ∈ P, ¬p ∣ q) :
    shiftTwoGroupOmega P (q*R) = shiftTwoGroupOmega P R := by
  classical
  unfold shiftTwoGroupOmega
  congr 1
  ext p
  by_cases hp : p ∈ P
  · have hiff : p ∣ q*R ↔ p ∣ R := by
      constructor
      · intro hMul
        rcases (hPrime p hp).dvd_mul.mp hMul with hq | hR
        · exact False.elim ((hNoP p hp) hq)
        · exact hR
      · intro hR
        exact dvd_mul_of_dvd_right hR q
    simp [Finset.mem_filter, hp, hiff]
  · simp [Finset.mem_filter, hp]

/- The literal marked W₁ weight is unaffected by multiplying by
an ordinary Q-factor free of P-primes. No probabilistic surrogates. -/



/- Exact source owner: SourceOriginalQPWeightedSupport.lean; original line 33. -/
theorem source_original_W1_nonP_mul
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (q R : ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hNoP : ∀ g p, p ∈ P g → ¬p ∣ q) :
    sourceOriginalW1 P (q*R) = sourceOriginalW1 P R := by
  classical
  unfold sourceOriginalW1
  apply Finset.prod_congr rfl
  intro g hg
  unfold shiftTwoOriginalGroupFactor
  rw [source_original_group_omega_nonP_mul
    (P g) q R (hPrime g) (hNoP g)]
/- Multiplicity-counted P-Omega is unaffected by multiplying by a
Q-factor having no P-prime divisor, for arbitrary repeated P powers. -/



/- Exact source owner: SourceOriginalQPNoprimeDivisors.lean; original line 9. -/
theorem source_original_prime_not_dvd_finset_product
    {I : Type} [DecidableEq I]
    (p : ℕ) (hp : p.Prime) (a : I → ℕ) (s : Finset I) :
    (∀ i ∈ s, ¬p ∣ a i) → ¬p ∣ ∏ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simpa using hp.ne_one
  | @insert i s hi ih =>
      intro hNo
      rw [Finset.prod_insert hi]
      intro hDiv
      rcases hp.dvd_mul.mp hDiv with hFirst | hSecond
      · exact (hNo i (Finset.mem_insert_self i s)) hFirst
      · exact (ih (fun j hj => hNo j (Finset.mem_insert_of_mem hj))) hSecond

/- Every literal complete labelled Q-assignment product contains no
prime from P, provided the actual Q and P prime bands are disjoint. -/



/- Exact source owner: SourceOriginalQPNoprimeDivisors.lean; original line 28. -/
theorem source_original_full_Q_product_no_P_prime
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    ∀ p ∈ Finset.univ.biUnion P,
      ¬ p ∣ (∏ b : B, ∏ i : Fin r, (f b i).val) := by
  intro p hpPall
  obtain ⟨g, hg, hpP⟩ := Finset.mem_biUnion.mp hpPall
  have hpPrime : p.Prime := hPPrime g p hpP
  apply source_original_prime_not_dvd_finset_product
    p hpPrime (fun b => ∏ i : Fin r, (f b i).val) Finset.univ
  intro b hb
  apply source_original_prime_not_dvd_finset_product
    p hpPrime (fun i : Fin r => (f b i).val) Finset.univ
  intro i hi hDiv
  have hqPrime := hQPrime b (f b i).val (f b i).property
  have heq := (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hDiv
  exact hQP b g p (heq ▸ (f b i).property) hpP
/- Product of all original Q slots does not perturb W1 or
multiplicity-counted P Omega when Q and P bands are genuinely disjoint. -/



/- Exact source owner: SourceOriginalQPNoprimeDivisors.lean; original line 52. -/
theorem source_original_full_Q_product_P_weight_invariant
    {B G : Type} [Fintype B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (R : ℕ) (hR : R ≠ 0)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    let q := ∏ b : B, ∏ i : Fin r, (f b i).val
    sourceOriginalW1 P (q*R) = sourceOriginalW1 P R ∧
    sourceOriginalPParityExponent (Finset.univ.biUnion P) (q*R) =
      sourceOriginalPParityExponent (Finset.univ.biUnion P) R := by
  intro q
  have hNo := source_original_full_Q_product_no_P_prime
    r Q P f hQPrime hPPrime hQP
  have hqNonzero : q ≠ 0 := by
    dsimp [q]
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (hQPrime b _ (f b i).property).ne_zero
  have hNoG : ∀ g p, p ∈ P g → ¬p ∣ q := by
    intro g p hpg
    exact hNo p (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hpg⟩)
  exact ⟨source_original_W1_nonP_mul P q R hPPrime hNoG,
      source_original_P_multiplicity_nonP_mul
        (Finset.univ.biUnion P) q R hqNonzero hR hNo⟩



/- Exact source owner: SourceOriginalQPFibreSamplingWeight.lean; original line 12. -/
theorem source_original_QP_fibre_sampling_weight_exact
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
    sourceOriginalQSamplingWeight (B:=B) r P (q*R.val) x Ψ =
      (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1-(-1:ℝ)^sourceOriginalPParityExponent
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
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent
       Pall (q*R.val))/2) * Ψ (((q*R.val:ℕ):ℝ)/x) = _
  rw [hWeight.1, hWeight.2]



/- Exact source owner: SourceShiftTwoAssignmentDecompose.lean; original line 9. -/
abbrev ShiftTwoMicroAssignments {J : Type}
    (r : ℕ) (Q : J → Finset ℕ) :=
  (j : J) → (Fin r → {p // p ∈ Q j})

/- Exactly one marked prime for EACH P_g. -/



/- Exact source owner: SourceShiftTwoOrbitSupport.lean; original line 8. -/
noncomputable def sourceShiftTwoMicroOrbit
    {J : Type} [Fintype J] [DecidableEq J]
    (r : ℕ) (Q : J → Finset ℕ)
    (f : ShiftTwoMicroAssignments r Q) :
    Finset (ShiftTwoMicroAssignments r Q) :=
  Fintype.piFinset (fun j : J =>
    Finset.univ.image (fun σ : Equiv.Perm (Fin r) => f j ∘ σ))

/- Every labelled permutation retains the FULL repeated-prime product. -/



/- Exact source owner: SourceShiftTwoXACanonicalSampling.lean; original line 10. -/
noncomputable def sourceOriginalFullQOrbitAt
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ) :
    Finset ((b : B) → Fin r → {p // p ∈ Q b}) :=
  if h : ∃ f : (b : B) → Fin r → {p // p ∈ Q b},
      (∏ b : B, ∏ i : Fin r, (f b i).val) = v then
    sourceShiftTwoMicroOrbit r Q (Classical.choose h)
  else ∅

/- No conditional tuple hypothesis: the full source coefficient is
exactly the sum over its chosen complete orbit. All factorials survive. -/



/- Exact source owner: SourceOriginalQPFibreEquiv.lean; original line 9. -/
def sourceOriginalOrdinaryFibre (Pall : Finset ℕ) (q : ℕ) : Type :=
  {u : ℕ // u ≠ 0 ∧ sourceOriginalOrdinaryPart Pall u = q}

/- Genuine unrestricted fibre correspondence. It follows from the
source's prime-power splitting, not a probability-space postulate. -/



/- Exact source owner: SourceOriginalQPFibreEquiv.lean; original line 14. -/
noncomputable def source_original_QP_ordinary_fibre_equiv
    (Pall : Finset ℕ) (q : ℕ)
    (hq : q ≠ 0)
    (hPrime : ∀ p ∈ Pall, p.Prime)
    (hNoP : ∀ p ∈ Pall, ¬p ∣ q) :
    sourceOriginalOrdinaryFibre Pall q ≃ sourceOriginalPSupported Pall where
  toFun u := by
    have hu := u.property.1
    have hSplit := source_original_ordinary_times_P_part Pall u.val hu
    have hPpos : sourceOriginalPPrimePart Pall u.val ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hSplit
      exact hu hSplit.symm
    refine ⟨sourceOriginalPPrimePart Pall u.val, hPpos, ?_⟩
    rw [source_original_P_prime_part_eq_vector_product Pall hPrime u.val hu]
    exact source_original_P_power_primeFactors_subset Pall hPrime _
  invFun R := ⟨q*R.val, mul_ne_zero hq R.property.1,
    source_original_QP_ordinary_part_product Pall q R hq hPrime hNoP⟩
  left_inv u := by
    apply Subtype.ext
    change q * sourceOriginalPPrimePart Pall u.val = u.val
    have hu := source_original_ordinary_times_P_part Pall u.val u.property.1
    rwa [u.property.2] at hu
  right_inv R := by
    apply Subtype.ext
    change sourceOriginalPPrimePart Pall (q*R.val) = R.val
    have hu := source_original_ordinary_times_P_part Pall
      (q*R.val) (mul_ne_zero hq R.property.1)
    rw [source_original_QP_ordinary_part_product
      Pall q R hq hPrime hNoP] at hu
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hu



/- Exact source owner: SourceOriginalQPFibreTsum.lean; original line 9. -/
theorem source_original_QP_fibre_finite_tsum
    (Pall : Finset ℕ) (q N : ℕ) (F : ℕ → ℝ)
    (hq : q ≠ 0) (hPrime : ∀ p ∈ Pall, p.Prime)
    (hNoP : ∀ p ∈ Pall, ¬p ∣ q)
    (hFzero : F 0 = 0) :
    (∑ u ∈ Finset.range N,
      if sourceOriginalOrdinaryPart Pall u = q then F u else 0) =
    ∑' R : sourceOriginalPSupported Pall,
      if q*R.val < N then F (q*R.val) else 0 := by
  classical
  let S : Set ℕ := {u | u ≠ 0 ∧ sourceOriginalOrdinaryPart Pall u = q}
  let E := source_original_QP_ordinary_fibre_equiv Pall q hq hPrime hNoP
  have hLeft : (∑ u ∈ Finset.range N,
      if sourceOriginalOrdinaryPart Pall u = q then F u else 0) =
      ∑' u : S, if (u.val:ℕ) < N then F u.val else 0 := by
    have hZero : (∑ u ∈ Finset.range N,
        if sourceOriginalOrdinaryPart Pall u = q then F u else 0) =
        ∑ u ∈ Finset.range N, if u ∈ S then F u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hz : u = 0
      · subst u
        simp [S, hFzero]
      · simp [S, hz]
    rw [hZero]
    have hIndicator :
        (∑' u : S, if (u.val:ℕ) < N then F u.val else 0) =
        ∑' u : ℕ, S.indicator (fun v => if v < N then F v else 0) u :=
      tsum_subtype S (fun v : ℕ => if v < N then F v else 0)
    rw [hIndicator]
    have hOff (u : ℕ) (hu : u ∉ Finset.range N) :
        S.indicator (fun v => if v < N then F v else 0) u = 0 := by
      have hnot : ¬ u < N := by simpa using hu
      simp [Set.indicator_apply, hnot]
    rw [tsum_eq_sum hOff]
    apply Finset.sum_congr rfl
    intro u hu
    have huN : u < N := Finset.mem_range.mp hu
    by_cases hs : u ∈ S
    · simp [Set.indicator_apply, huN, hs]
    · simp [Set.indicator_apply, hs]
  calc
    _ = ∑' u : S, if (u.val:ℕ) < N then F u.val else 0 := hLeft
    _ = ∑' u : S, if q * (E u).val < N then F (q*(E u).val) else 0 := by
      apply tsum_congr
      intro u
      have hu : q * (E u).val = u.val := by
        change q * sourceOriginalPPrimePart Pall u.val = u.val
        rw [← u.property.2]
        exact source_original_ordinary_times_P_part Pall u.val u.property.1
      rw [hu]
    _ = ∑' R : sourceOriginalPSupported Pall,
        if q*R.val < N then F (q*R.val) else 0 :=
      E.tsum_eq (fun R : sourceOriginalPSupported Pall =>
        if q*R.val < N then F (q*R.val) else 0)



/- Exact source owner: SourceShiftTwoMacroDrop.lean; original line 22. -/
theorem source_factorial_band_to_tuple
    (r : ℕ) (Q : Finset ℕ)
    (f : Fin r → {p // p ∈ Q}) (v : ℕ)
    (hval : ∀ p ∈ Q, v.factorization p =
      ((Finset.univ : Finset (Fin r)).filter
        (fun i => (f i).val = p)).card) :
    (∏ p ∈ Q, (((v.factorization p).factorial:ℝ)⁻¹)) =
      ∏ p ∈ Finset.univ.image f,
        ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)⁻¹ := by
  classical
  let S : Finset {p // p ∈ Q} := Finset.univ.image f
  have hmissing (p : {p // p ∈ Q}) (hp : p ∈ (Finset.univ : Finset {p // p ∈ Q}))
      (hn : p ∉ S) :
      (((v.factorization p.val).factorial:ℝ)⁻¹) = 1 := by
    have hzero : v.factorization p.val = 0 := by
      rw [hval p.val p.property]
      apply Finset.card_eq_zero.mpr
      ext i
      have hne : f i ≠ p := by
        intro he
        exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hne]
    simp [hzero]
  calc
    (∏ p ∈ Q, (((v.factorization p).factorial:ℝ)⁻¹)) =
      ∏ p : {n // n ∈ Q}, (((v.factorization p.val).factorial:ℝ)⁻¹) :=
        (Finset.prod_coe_sort Q _).symm
    _ = ∏ p ∈ S, (((v.factorization p.val).factorial:ℝ)⁻¹) := by
      exact (Finset.prod_subset (Finset.subset_univ S) hmissing).symm
    _ = ∏ p ∈ S, ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hc : Fintype.card {i : Fin r // f i = p} =
          ((Finset.univ : Finset (Fin r)).filter
            (fun i => (f i).val = p.val)).card := by
        simp only [Fintype.card_subtype, Subtype.ext_iff]
      rw [hval p.val p.property, hc]

/- Source a(v) really includes the MACRO Q bands. They can be
discarded only after the full tuple-support witness is used, because
their genuine factorial factors are each at most one. The remaining
micro factorials are bounded by the EXISTING all-bands orbit theorem. -/



/- Exact source owner: SourceShiftTwoLiteralWeights.lean; original line 10. -/
theorem source_prime_tuple_factorization_count
    {I : Type} [Fintype I] (f : I → ℕ)
    (hf : ∀ i, (f i).Prime) (p : ℕ) :
    (∏ i, f i).factorization p =
      ((Finset.univ : Finset I).filter (fun i => f i = p)).card := by
  classical
  have hn : ∀ i ∈ (Finset.univ : Finset I), f i ≠ 0 := by
    intro i hi
    exact (hf i).ne_zero
  rw [Nat.factorization_prod hn]
  simp only [Finsupp.finset_sum_apply]
  simp_rw [Nat.Prime.factorization (hf _)]
  simp only [Finsupp.single_apply]
  simp [Finset.sum_ite]



/- Exact source owner: SourceShiftTwoFullSlots.lean; original line 9. -/
theorem source_full_slots_band_factorization
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (f : (b : B) → (Fin r → {p // p ∈ Q b}))
    (b0 : B) (p : ℕ) (hp : p ∈ Q b0) :
    (∏ b : B, ∏ i : Fin r, (f b i).val).factorization p =
      ((Finset.univ : Finset (Fin r)).filter
         (fun i => (f b0 i).val = p)).card := by
  classical
  have hNonzero (b : B) : (∏ i : Fin r, (f b i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact (hPrime b _ (f b i).property).ne_zero)
  have hFactor : (∏ b : B, ∏ i : Fin r, (f b i).val).factorization p =
       ∑ b : B, ((Finset.univ : Finset (Fin r)).filter
           (fun i => (f b i).val = p)).card := by
    rw [Nat.factorization_prod (by intro b hb; exact hNonzero b)]
    simp only [Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl (fun b hb =>
      source_prime_tuple_factorization_count
        (fun i : Fin r => (f b i).val)
        (fun i => hPrime b _ (f b i).property) p)
  rw [hFactor]
  apply Finset.sum_eq_single b0
  · intro b hb hneq
    apply Finset.card_eq_zero.mpr
    ext i
    have hne : (f b i).val ≠ p := by
      intro heq
      exact hneq (hDisjoint b b0 p (heq ▸ (f b i).property) hp)
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ b0))


end Green64Analytic.SourceBlockSieve

namespace Green64FiniteExtraction


/- Exact source owner: Assignments.lean; original line 359. -/
theorem micro_factorial_tuples :
  ∀ {α : Type} [DecidableEq α] (r : ℕ) (f : Fin r → α),
   (∑ a ∈ (Finset.univ.image (fun σ : Equiv.Perm (Fin r) => f ∘ σ)),
        (1:ℝ)/(r.factorial:ℝ)) =
   ∏ p ∈ Finset.univ.image f,
        ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)⁻¹ :=
by
 have fact : ∀ {α : Type} [DecidableEq α] (r : ℕ) (f : Fin r → α),
 ((Nat.card (MulAction.orbit (DomMulAct (Equiv.Perm (Fin r))) f)):ℝ) /
      (r.factorial:ℝ) =
 ∏ p ∈ Finset.univ.image f,
      ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)⁻¹ := by
  classical
  intro α _ r f
  let G := DomMulAct (Equiv.Perm (Fin r))
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin r)) DomMulAct.mk
  letI : Fintype (MulAction.orbit G f) := (Finite.finite_mulAction_orbit (M := G) f).fintype
  letI : Fintype (MulAction.stabilizer G f) := Fintype.ofFinite _
  let e : (MulAction.stabilizer G f) ≃
        {g : Equiv.Perm (Fin r) // f ∘ g = f} :=
    { toFun := fun g => ⟨DomMulAct.mk.symm g.val,
         (DomMulAct.mem_stabilizer_iff (f := f)).mp g.property⟩
      invFun := fun g => ⟨DomMulAct.mk g.val,
         (DomMulAct.mem_stabilizer_iff (f := f)).mpr g.property⟩
      left_inv := fun g => by rfl
      right_inv := fun g => by rfl }
  have hs : Fintype.card (MulAction.stabilizer G f) =
        ∏ p ∈ Finset.univ.image f, (Fintype.card {i : Fin r // f i = p}).factorial := by
    rw [Fintype.card_congr e]
    exact DomMulAct.stabilizer_card' f
  have hg : Fintype.card G = r.factorial := by
    rw [← Fintype.card_congr (DomMulAct.mk : Equiv.Perm (Fin r) ≃ G)]
    simp [Fintype.card_perm]
  have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G f
  rw [hs,hg] at hc
  have hcr : (Fintype.card (MulAction.orbit G f):ℝ) *
        (∏ p ∈ Finset.univ.image f, ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)) =
        (r.factorial:ℝ) := by exact_mod_cast hc
  have hd : (r.factorial:ℝ) ≠ 0 := by positivity
  have hp : (∏ p ∈ Finset.univ.image f,
        ((Fintype.card {i : Fin r // f i = p}).factorial:ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    positivity
  rw [Nat.card_eq_fintype_card]
  change (Fintype.card (MulAction.orbit G f):ℝ) / (r.factorial:ℝ) = _
  rw [Finset.prod_inv_distrib]
  apply (div_eq_iff hd).mpr
  field_simp [hp]
  nlinarith [hcr]
 classical
 intro α _ r f
 let G := DomMulAct (Equiv.Perm (Fin r))
 let O := Finset.univ.image (fun σ : Equiv.Perm (Fin r) => f ∘ σ)
 let e : (MulAction.orbit G f) ≃ {a // a ∈ O} :=
   { toFun := fun a => ⟨a.val, by
       rcases a.property with ⟨g,hg⟩
       exact Finset.mem_image.mpr ⟨DomMulAct.mk.symm g, Finset.mem_univ _, hg⟩⟩
     invFun := fun a => ⟨a.val, by
       rcases Finset.mem_image.mp a.property with ⟨g,hg,he⟩
       exact ⟨DomMulAct.mk g, he⟩⟩
     left_inv := fun a => rfl
     right_inv := fun a => rfl }
 have he : Nat.card (MulAction.orbit G f) = O.card := by
   rw [Nat.card_congr e]
   simp
 have hf := fact r f
 change (Nat.card (MulAction.orbit G f):ℝ) / (r.factorial:ℝ) = _ at hf
 rw [he] at hf
 simpa [O, div_eq_mul_inv] using hf

/- Exact proposition checked by group-mark-size-asymptotic-02. See the paired request and receipt. -/


end Green64FiniteExtraction

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoOrbitSupport.lean; original line 37. -/
theorem source_micro_orbit_mass_equals_factorials
    {J : Type} [Fintype J] [DecidableEq J]
    (r : ℕ) (Q : J → Finset ℕ)
    (f : ShiftTwoMicroAssignments r Q) :
    (∑ a ∈ sourceShiftTwoMicroOrbit r Q f,
       ∏ _j : J, (1:ℝ)/(r.factorial:ℝ)) =
      ∏ j : J, ∏ p ∈ Finset.univ.image (f j),
        ((Fintype.card {i : Fin r // f j i = p}).factorial:ℝ)⁻¹ := by
  classical
  let c : ℝ := (1:ℝ)/(r.factorial:ℝ)
  let orbits (j : J) : Finset (Fin r → {p // p ∈ Q j}) :=
    Finset.univ.image (fun σ : Equiv.Perm (Fin r) => f j ∘ σ)
  calc
    (∑ a ∈ sourceShiftTwoMicroOrbit r Q f,
       ∏ _j : J, (1:ℝ)/(r.factorial:ℝ)) =
      ∏ j : J, ∑ x ∈ orbits j, c := by
        exact (Finset.prod_univ_sum orbits (fun _j _a => c)).symm
    _ = ∏ j : J, ∏ p ∈ Finset.univ.image (f j),
          ((Fintype.card {i : Fin r // f j i = p}).factorial:ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro j hj
        exact Green64FiniteExtraction.micro_factorial_tuples r (f j)



/- Exact source owner: SourceShiftTwoXAFactorialOrbit.lean; original line 9. -/
theorem source_original_full_Q_factorial_orbit
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (f : (b : B) → Fin r → {p // p ∈ Q b})
    (hf : (∏ b : B, ∏ i : Fin r, (f b i).val) = v)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalOrdinaryCoefficient r Q v =
      ∑ a ∈ sourceShiftTwoMicroOrbit r Q f,
        ∏ _b : B, (1:ℝ)/(r.factorial:ℝ) := by
  classical
  have hCounts (b : B) (p : ℕ) (hp : p ∈ Q b) :
      v.factorization p =
        ((Finset.univ : Finset (Fin r)).filter
          (fun i => (f b i).val = p)).card := by
    have h := source_full_slots_band_factorization
      r Q hPrime hDisjoint f b p hp
    rw [hf] at h
    exact h
  calc
    sourceOriginalOrdinaryCoefficient r Q v =
        ∏ b : B, ∏ p ∈ Q b,
          (((v.factorization p).factorial:ℝ)⁻¹) := by
            unfold sourceOriginalOrdinaryCoefficient
            rw [if_pos ⟨f, hf⟩]
    _ = ∏ b : B, ∏ p ∈ Finset.univ.image (f b),
          ((Fintype.card {i : Fin r // f b i = p}).factorial:ℝ)⁻¹ := by
            apply Finset.prod_congr rfl
            intro b hb
            exact source_factorial_band_to_tuple r (Q b) (f b) v
              (hCounts b)
    _ = ∑ a ∈ sourceShiftTwoMicroOrbit r Q f,
          ∏ _b : B, (1:ℝ)/(r.factorial:ℝ) :=
            (source_micro_orbit_mass_equals_factorials r Q f).symm

/- Source A with genuine W1, odd multiplicity parity, and cutoff:
the entire ordinary coefficient, not a micro-only majorant. -/



/- Exact source owner: SourceShiftTwoXACanonicalSampling.lean; original line 21. -/
theorem source_original_full_Q_coefficient_finite_sampling
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalOrdinaryCoefficient r Q v =
      ∑ f ∈ sourceOriginalFullQOrbitAt r Q v,
        ∏ _b : B, (1:ℝ)/(r.factorial:ℝ) := by
  classical
  unfold sourceOriginalFullQOrbitAt
  split_ifs with h
  · exact source_original_full_Q_factorial_orbit
      r Q v (Classical.choose h) (Classical.choose_spec h)
      hPrime hDisjoint
  · simp [sourceOriginalOrdinaryCoefficient, h]
/- A genuine finite identity for the ORIGINAL source X_A itself.
Unlike a new candidate or a simplified probability model, the sums
are literally the source's u<=floor(2*x), omega_g distinct-count
W1, multiplicity-parity, Psi, and r! per complete Q-band. -/



/- Exact source owner: SourceShiftTwoXACanonicalSampling.lean; original line 40. -/
theorem source_original_XA_complete_orbit_finite_sampling
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalXA r Q P x Ψ =
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        ∑ f ∈ sourceOriginalFullQOrbitAt r Q
              (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u),
          (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
            sourceOriginalW1 P u *
            ((1 - (-1:ℝ)^sourceOriginalPParityExponent
                 (Finset.univ.biUnion P) u)/2) *
            Ψ ((u:ℝ)/x) := by
  classical
  unfold sourceOriginalXA
  apply Finset.sum_congr rfl
  intro u hu
  rw [sourceOriginalA, sourceOriginalA0,
    source_original_full_Q_coefficient_finite_sampling
      r Q _ hPrime hDisjoint]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  ring



/- Exact source owner: SourceShiftTwoOrbitSupport.lean; original line 17. -/
theorem source_micro_orbit_product_eq
    {J : Type} [Fintype J] [DecidableEq J]
    (r : ℕ) (Q : J → Finset ℕ)
    (f a : ShiftTwoMicroAssignments r Q)
    (ha : a ∈ sourceShiftTwoMicroOrbit r Q f) :
    (∏ j : J, ∏ i : Fin r, (a j i).val) =
      (∏ j : J, ∏ i : Fin r, (f j i).val) := by
  classical
  unfold sourceShiftTwoMicroOrbit at ha
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := (Fintype.mem_piFinset.mp ha) j
  obtain ⟨σ,hσ,hσa⟩ := Finset.mem_image.mp hj'
  change (∏ i : Fin r, (a j i).val) = (∏ i : Fin r, (f j i).val)
  rw [←hσa]
  simpa only [Function.comp_apply] using
    (Equiv.prod_comp σ (fun i : Fin r => (f j i).val))

/- Exact reused factorial orbit count, valid for REPEATED primes in
each Q band. -/



/- Exact source owner: SourceShiftTwoXAOrbitProduct.lean; original line 8. -/
theorem source_original_canonical_orbit_product_eq
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (a : (b : B) → Fin r → {p // p ∈ Q b})
    (ha : a ∈ sourceOriginalFullQOrbitAt r Q v) :
    (∏ b : B, ∏ i : Fin r, (a b i).val) = v := by
  classical
  unfold sourceOriginalFullQOrbitAt at ha
  split_ifs at ha with h
  · exact (source_micro_orbit_product_eq r Q (Classical.choose h) a ha).trans
      (Classical.choose_spec h)
  · simp at ha

/- On every positive original candidate, the sampled ordinary slots
and the exact group prime-power part multiply to the ACTUAL u. -/



/- Exact source owner: SourceXAOrbitFibrePerm.lean; original line 9. -/
theorem source_finite_equal_fibres_give_perm
    {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]
    (f g : I → A)
    (hCount : ∀ a : A,
      Fintype.card {i : I // f i = a} =
      Fintype.card {i : I // g i = a}) :
    ∃ σ : Equiv.Perm I, ∀ i : I, f (σ i) = g i := by
  classical
  let E (a : A) : {i : I // f i = a} ≃ {i : I // g i = a} :=
    Fintype.equivOfCardEq (hCount a)
  let σ : Equiv.Perm I :=
    (Equiv.sigmaFiberEquiv g).symm |>.trans
      ((Equiv.sigmaCongrRight (fun a : A => (E a).symm)).trans
        (Equiv.sigmaFiberEquiv f))
  refine ⟨σ, ?_⟩
  intro i
  change f (((E (g i)).symm ⟨i,rfl⟩).val) = g i
  exact ((E (g i)).symm ⟨i,rfl⟩).property



/- Exact source owner: SourceXAOrbitProductFibres.lean; original line 10. -/
theorem source_original_full_Q_equal_product_band_perm
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ)
    (f g : (b : B) → Fin r → {p // p ∈ Q b})
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hEq : (∏ b : B, ∏ i : Fin r, (f b i).val) =
      (∏ b : B, ∏ i : Fin r, (g b i).val)) :
    ∀ b : B, ∃ σ : Equiv.Perm (Fin r),
        ∀ i : Fin r, f b (σ i) = g b i := by
  intro b
  have hCounts (a : {p // p ∈ Q b}) :
      Fintype.card {i : Fin r // f b i = a} =
      Fintype.card {i : Fin r // g b i = a} := by
    have hF := source_full_slots_band_factorization
      r Q hPrime hDisjoint f b a.val a.property
    have hG := source_full_slots_band_factorization
      r Q hPrime hDisjoint g b a.val a.property
    have hValues :
        ((Finset.univ : Finset (Fin r)).filter
          (fun i => (f b i).val = a.val)).card =
        ((Finset.univ : Finset (Fin r)).filter
          (fun i => (g b i).val = a.val)).card := by
      calc
        _ = (∏ b : B, ∏ i : Fin r, (f b i).val).factorization a.val :=
          hF.symm
        _ = (∏ b : B, ∏ i : Fin r, (g b i).val).factorization a.val :=
          congrArg (fun n : ℕ => n.factorization a.val) hEq
        _ = _ := hG
    simpa only [Fintype.card_subtype, Subtype.ext_iff]
      using hValues
  exact source_finite_equal_fibres_give_perm (f b) (g b) hCounts
/- The full labelled product is a complete invariant of
the canonical factorial orbit, with repeated primes permitted. -/



/- Exact source owner: SourceXAOrbitProductFibres.lean; original line 44. -/
theorem source_original_full_Q_equal_product_same_orbit
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ)
    (f g : (b : B) → Fin r → {p // p ∈ Q b})
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hEq : (∏ b : B, ∏ i : Fin r, (f b i).val) =
      (∏ b : B, ∏ i : Fin r, (g b i).val)) :
    g ∈ sourceShiftTwoMicroOrbit r Q f := by
  classical
  have hPerm := source_original_full_Q_equal_product_band_perm
    r Q f g hPrime hDisjoint hEq
  let σ (b : B) : Equiv.Perm (Fin r) := Classical.choose (hPerm b)
  have hs (b : B) (i : Fin r) : f b (σ b i) = g b i :=
    Classical.choose_spec (hPerm b) i
  unfold sourceShiftTwoMicroOrbit
  apply Fintype.mem_piFinset.mpr
  intro b
  apply Finset.mem_image.mpr
  refine ⟨σ b, Finset.mem_univ _, ?_⟩
  funext i
  exact hs b i



/- Exact source owner: SourceXAOrbitMembershipProduct.lean; original line 10. -/
theorem source_original_full_Q_canonical_orbit_iff_product
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (a : (b : B) → Fin r → {p // p ∈ Q b})
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    a ∈ sourceOriginalFullQOrbitAt r Q v ↔
      (∏ b : B, ∏ i : Fin r, (a b i).val) = v := by
  constructor
  · exact source_original_canonical_orbit_product_eq r Q v a
  · intro hProduct
    classical
    unfold sourceOriginalFullQOrbitAt
    split_ifs with h
    · have hChosen := Classical.choose_spec h
      exact source_original_full_Q_equal_product_same_orbit
        r Q (Classical.choose h) a hPrime hDisjoint
        (hChosen.trans hProduct.symm)
    · exact False.elim (h ⟨a,hProduct⟩)

/- A complete sampling tuple belongs to the canonical orbit
for the actual u if and only if its literal Q product equals u_*.
This removes the arbitrary representative choice entirely. -/



/- Exact source owner: SourceOriginalQPXADisintegration.lean; original line 12. -/
theorem source_original_XA_full_QP_tsum_disintegration
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    sourceOriginalXA r Q P x Ψ =
      ∑ f : (b : B) → Fin r → {p // p ∈ Q b},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          if (∏ b : B, ∏ i : Fin r, (f b i).val) * R.val < ⌊2*x⌋₊+1
          then sourceOriginalQSamplingWeight (B:=B) r P
            ((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) x Ψ
          else 0 := by
  classical
  let A := (b : B) → Fin r → {p // p ∈ Q b}
  let Pall : Finset ℕ := Finset.univ.biUnion P
  let N : ℕ := ⌊2*x⌋₊+1
  let q (f : A) : ℕ := ∏ b : B, ∏ i : Fin r, (f b i).val
  let w (u : ℕ) : ℝ := sourceOriginalQSamplingWeight (B:=B) r P u x Ψ
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g, hg, hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPPrime g p hpg
  have hw0 : w 0 = 0 := by
    simp [w, sourceOriginalQSamplingWeight, sourceOriginalPParityExponent]
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
    sourceOriginalXA r Q P x Ψ =
        ∑ u ∈ Finset.range N,
          ∑ f : A, if q f = sourceOriginalOrdinaryPart Pall u
            then w u else 0 := by
              rw [source_original_XA_complete_orbit_finite_sampling
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



/- Exact source owner: SourceOriginalQPXALiteralWeights.lean; original line 11. -/
theorem source_original_XA_QP_literal_weights_exact
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    sourceOriginalXA r Q P x Ψ =
      ∑ f : (b : B) → Fin r → {p // p ∈ Q b},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          if (∏ b : B, ∏ i : Fin r, (f b i).val) * R.val < ⌊2*x⌋₊+1
          then (∏ _b : B, (1:ℝ)/(r.factorial:ℝ)) *
            sourceOriginalW1 P R.val *
            ((1 - (-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion P) R.val)/2) *
            Ψ (((((∏ b : B, ∏ i : Fin r, (f b i).val) * R.val) : ℕ) : ℝ) / x)
          else 0 := by
  rw [source_original_XA_full_QP_tsum_disintegration
    r Q P x Ψ hQPrime hQDisj hPPrime hQP]
  apply Finset.sum_congr rfl
  intro f hf
  apply tsum_congr
  intro R
  split_ifs with hCut
  · exact (source_original_QP_fibre_sampling_weight_exact
      r Q P f R x Ψ hQPrime hPPrime hQP).2
  · rfl



/- Exact source owner: SourceOriginalQPFreeSlotTsum.lean; original line 11. -/
theorem source_original_XA_full_QP_free_slot_exact
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    sourceOriginalXA r Q P x Ψ =
      ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        ∑ p : {p // p ∈ Q b},
          ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
            let f := (sourceOriginalQSlotsCurryEquiv r Q)
              ((Equiv.piSplitAt (b,i)
                (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
                (p,rest))
            if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
            then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0 := by
  classical
  let A := (j : B) → Fin r → {p // p ∈ Q j}
  let S := (k : B × Fin r) → {p // p ∈ Q k.1}
  let e : S ≃ A := sourceOriginalQSlotsCurryEquiv r Q
  let w (f : A) : ℝ :=
    ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
      then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0
  calc
    sourceOriginalXA r Q P x Ψ = ∑ f : A, w f := by
      simpa only [w, sourceOriginalQPLiteralTerm, A] using
        source_original_XA_QP_literal_weights_exact
          r Q P x Ψ hQPrime hQDisj hPPrime hQP
    _ = ∑ g : S, w (e g) := (Equiv.sum_comp e w).symm
    _ = ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
          ∑ p : {p // p ∈ Q b},
            w (e ((Equiv.piSplitAt (b,i)
              (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
              (p,rest))) :=
        source_full_Q_one_free_slot_sum r Q b i (fun g : S => w (e g))
    _ = _ := rfl



/- Exact source owner: SourceOriginalQPFreeSlotFubini.lean; original line 11. -/
theorem source_original_XA_QP_free_prime_inside_P_tsum
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
    (hQPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hQDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hPPrime : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    sourceOriginalXA r Q P x Ψ =
      ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) →
          {p // p ∈ Q k.1.1},
        ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
          ∑ p : {p // p ∈ Q b},
            let f := (sourceOriginalQSlotsCurryEquiv r Q)
              ((Equiv.piSplitAt (b,i)
                (fun k : B × Fin r => {p // p ∈ Q k.1})).symm
                (p,rest))
            if (∏ j : B, ∏ m : Fin r, (f j m).val) * R.val < ⌊2*x⌋₊+1
            then sourceOriginalQPLiteralTerm r Q P x Ψ f R else 0 := by
  classical
  rw [source_original_XA_full_QP_free_slot_exact
    r Q P b i x Ψ hQPrime hQDisj hPPrime hQP]
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
    sourceOriginalQPLiteralTerm r Q P x Ψ (t p) R
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



/- Exact source owner: SourceOriginalQPRestPruning.lean; original line 88. -/
theorem source_original_XA_QP_good_rest_lower
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (x : ℝ) (Ψ : ℝ → ℝ)
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
           sourceOriginalQPActualFreeTerm r Q P b i x Ψ rest R else 0) ≤
    sourceOriginalXA r Q P x Ψ := by
  classical
  rw [source_original_XA_QP_free_prime_inside_P_tsum
    r Q P b i x Ψ hQPrime hQDisj hPPrime hQP]
  apply Finset.sum_le_sum
  intro rest hrest
  let v : sourceOriginalPSupported (Finset.univ.biUnion P) → ℝ :=
    sourceOriginalQPActualFreeTerm r Q P b i x Ψ rest
  have hNonneg (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
      0 ≤ v R :=
    source_original_QP_actual_free_term_nonneg r Q P b i x Ψ hΨ rest R
  have hFull : Summable v :=
    source_original_QP_actual_free_term_summable
      r Q P b i x Ψ hQPrime rest
  have hLe (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :
      (if Good rest R then v R else 0) ≤ v R := by
    split_ifs <;> [exact le_rfl; exact hNonneg R]
  have hRestricted : Summable (fun R : sourceOriginalPSupported
      (Finset.univ.biUnion P) => if Good rest R then v R else 0) :=
    hFull.of_nonneg_of_le (fun R => by split_ifs <;> [exact hNonneg R; exact le_rfl]) hLe
  change (∑' R, if Good rest R then v R else 0) ≤ ∑' R, v R
  exact Summable.tsum_le_tsum hLe hRestricted hFull



/- Exact source owner: SourceShiftTwoOriginalQ0Window.lean; original line 11. -/
noncomputable def sourceFreePrimeWindow (ell h : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp ell⌋₊ ⌊Real.exp (ell+h)⌋₊).filter Nat.Prime

/- The free-slot window is a subset of the literal source closed Q₀ band.
Endpoint conversion is exact (natCeil at the lower source endpoint). -/



/- Exact source owner: SourceShiftTwoOriginalQ0Window.lean; original line 16. -/
theorem source_free_prime_window_subset_original_Q0
    (L s ell h : ℝ)
    (hLow : s*L ≤ ell)
    (hHigh : ell+h ≤ (6/5:ℝ)*s*L) :
    sourceFreePrimeWindow ell h ⊆
      sourceClosedPrimeLogBand L s ((6/5:ℝ)*s) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRange,hPrime⟩
  have hRange := Finset.mem_Ioc.mp hpRange
  have hNat : (⌊Real.exp ell⌋₊:ℝ)+1 ≤ (p:ℝ) := by
    exact_mod_cast hRange.1
  have hFloor : Real.exp ell < (⌊Real.exp ell⌋₊:ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hpLow : Real.exp (s*L) ≤ (p:ℝ) := by
    have hExp := Real.exp_le_exp.mpr hLow
    linarith
  have hCeil : ⌈Real.exp (s*L)⌉₊ ≤ p := (Nat.ceil_le).2 hpLow
  have hTop : Real.exp (ell+h) ≤
      Real.exp ((6/5:ℝ)*s*L) :=
    Real.exp_le_exp.mpr (by convert hHigh using 1 <;> ring)
  have hFloorTop : ⌊Real.exp (ell+h)⌋₊ ≤
      ⌊Real.exp ((6/5:ℝ)*s*L)⌋₊ :=
    Nat.floor_le_floor hTop
  have hpTop : p ≤ ⌊Real.exp ((6/5:ℝ)*s*L)⌋₊ :=
    hRange.2.trans hFloorTop
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hCeil, hpTop⟩,hPrime⟩

/- Exact conversion from the PNT2 if-prime mass to its literal
finite prime-set form. No squarefree replacement. -/



/- Exact source owner: SourceShiftTwoPositiveFreeWindow.lean; original line 9. -/
theorem log_one_plus_lower_half
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z/2 ≤ Real.log (1+z) := by
  have hlog := Real.le_log_one_add_of_nonneg hz
  have hden : 0 < z+2 := by linarith
  have hsq : 0 ≤ z*(1-z) := mul_nonneg hz (by linarith)
  have hm : (z/2)*(z+2) ≤ 2*z := by nlinarith
  exact ((le_div_iff₀ hden).2 hm).trans hlog

/- A real PNT2 remainder, without Type II or a parity surrogate,
implies the correct 1/log(U) mass in every fixed-log-width prime window. -/



/- Exact source owner: SourceShiftTwoSharpShortWindow.lean; original line 12. -/
theorem source_prime_reciprocal_error_sharp
    (U V C : ℝ) (hU : 1 < U) (hUV : U ≤ V) (hC : 0 ≤ C)
    (hPNT : ∀ t ∈ Set.Icc U V,
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t|
        ≤ C*t/(Real.log t)^2) :
    |(∑ p ∈ Finset.Ioc ⌊U⌋₊ ⌊V⌋₊,
         if p.Prime then (p:ℝ)⁻¹ else 0)
       - Real.log (Real.log V / Real.log U)| ≤
    C/(Real.log V)^2 + C/(Real.log U)^2 +
       (C/(Real.log U)^2)*Real.log (V/U) +
       Real.log (V/U)/(Real.log U*Real.log V) := by
  have hV : 1 < V := hU.trans_le hUV
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hV0 : 0 < V := lt_trans zero_lt_one hV
  have hlu : 0 < Real.log U := Real.log_pos hU
  have hlv : 0 < Real.log V := Real.log_pos hV
  have hlogle : Real.log U ≤ Real.log V :=
    Real.log_le_log hU0 hUV
  have hInv :
      |(Real.log V)⁻¹ - (Real.log U)⁻¹| =
        Real.log (V/U)/(Real.log U*Real.log V) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ hlu hlogle))]
    rw [Real.log_div (ne_of_gt hV0) (ne_of_gt hU0)]
    field_simp
    <;> ring
  have hRem :=
    Green64Analytic.ReciprocalPrimeGrid.pnt2_abel_remainder
      Green64Analytic.ReciprocalPrimeGrid.primeRemainder
      U V C hU hUV hC hPNT
  have hId :=
    Green64Analytic.ReciprocalPrimeGrid.prime_reciprocal_error_identity
      U V hU hUV
  rw [hId]
  calc
    |Green64Analytic.ReciprocalPrimeGrid.primeRemainder V / V -
        Green64Analytic.ReciprocalPrimeGrid.primeRemainder U / U +
        (∫ t in U..V,
          Green64Analytic.ReciprocalPrimeGrid.primeRemainder t / t^2) +
        ((Real.log V)⁻¹ - (Real.log U)⁻¹)| ≤
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder V / V -
        Green64Analytic.ReciprocalPrimeGrid.primeRemainder U / U +
        (∫ t in U..V,
          Green64Analytic.ReciprocalPrimeGrid.primeRemainder t / t^2)| +
      |(Real.log V)⁻¹ - (Real.log U)⁻¹| := abs_add_le _ _
    _ ≤ _ := by rw [hInv]; linarith only [hRem]



/- Exact source owner: SourceShiftTwoPositiveFreeWindow.lean; original line 20. -/
theorem source_prime_free_window_lower_of_pnt2
    (ell h C : ℝ) (hell : 1 ≤ ell) (hh : 0 < h)
    (hC : 0 ≤ C) (hsmall : h ≤ ell)
    (hscale : 4*(2*C+C*h+h) ≤ h*ell)
    (hPNT : ∀ t, Real.exp ell ≤ t →
       |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t|
         ≤ C*t/(Real.log t)^2) :
    h/(4*ell) ≤
      ∑ p ∈ Finset.Ioc ⌊Real.exp ell⌋₊ ⌊Real.exp (ell+h)⌋₊,
         if p.Prime then (p:ℝ)⁻¹ else 0 := by
  have he : 0 < ell := by linarith
  have he1 : 1 < Real.exp ell := by
    simpa using (Real.exp_lt_exp.mpr he : Real.exp 0 < Real.exp ell)
  have hUleV : Real.exp ell ≤ Real.exp (ell+h) :=
    Real.exp_le_exp.mpr (by linarith)
  have hRatio : Real.log (Real.exp (ell+h)/Real.exp ell) = h := by
    rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
        Real.log_exp, Real.log_exp]
    ring
  have hPNT' : ∀ t ∈ Set.Icc (Real.exp ell) (Real.exp (ell+h)),
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t|
        ≤ C*t/(Real.log t)^2 :=
    fun t ht => hPNT t ht.1
  have hSharp :=
    source_prime_reciprocal_error_sharp
      (Real.exp ell) (Real.exp (ell+h)) C he1 hUleV hC hPNT'
  simp only [Real.log_exp, hRatio] at hSharp
  have hC1 : C/(ell+h)^2 ≤ C/ell^2 := by gcongr; linarith
  have hC2 : h/(ell*(ell+h)) ≤ h/ell^2 := by
    gcongr
    nlinarith
  have hErr :
      |(∑ p ∈ Finset.Ioc ⌊Real.exp ell⌋₊ ⌊Real.exp (ell+h)⌋₊,
          if p.Prime then (p:ℝ)⁻¹ else 0)
        - Real.log ((ell+h)/ell)| ≤ (2*C+C*h+h)/ell^2 := by
    calc
      _ ≤ C/(ell+h)^2 + C/ell^2 +
             (C/ell^2)*h + h/(ell*(ell+h)) := hSharp
      _ ≤ C/ell^2 + C/ell^2 + (C/ell^2)*h + h/ell^2 := by
        gcongr
      _ = (2*C+C*h+h)/ell^2 := by ring
  have hz : 0 ≤ h/ell := div_nonneg hh.le he.le
  have hzle : h/ell ≤ 1 := (div_le_one he).2 hsmall
  have hlog : h/(2*ell) ≤ Real.log ((ell+h)/ell) := by
    have h1 := log_one_plus_lower_half (h/ell) hz hzle
    have hid : (ell+h)/ell = 1 + h/ell := by
      field_simp
      <;> ring
    rw [hid]
    convert h1 using 1 <;> ring
  have herrorSmall : (2*C+C*h+h)/ell^2 ≤ h/(4*ell) := by
    have hden : 0 < ell^2 := sq_pos_of_pos he
    have hden' : 0 < 4*ell := by positivity
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) he.le]
  have habs := abs_le.mp (hErr.trans herrorSmall)
  have hhalf : h/(2*ell) = 2*(h/(4*ell)) := by
    field_simp
    <;> ring
  rw [hhalf] at hlog
  linarith only [hlog, habs.1]



/- Exact source owner: SourceShiftTwoUniformFreeWindow.lean; original line 13. -/
theorem source_free_prime_window_uniform
    (a M h : ℝ) (ha : 0 < a) (haM : a ≤ M) (hh : 0 < h) :
    ∀ᶠ L : ℝ in atTop,
       ∀ u, a ≤ u → u ≤ M →
         h/(4*M*L) ≤
           ∑ p ∈ Finset.Ioc ⌊Real.exp (u*L)⌋₊
                                 ⌊Real.exp (u*L+h)⌋₊,
             if p.Prime then (p:ℝ)⁻¹ else 0 := by
  obtain ⟨C, hC, hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hh0 : h*a ≠ 0 := mul_ne_zero (ne_of_gt hh) ha0
  filter_upwards [hPNT, eventually_gt_atTop (0:ℝ),
      eventually_ge_atTop (1/a), eventually_ge_atTop (h/a),
      eventually_ge_atTop (4*(2*C+C*h+h)/(h*a))]
    with L hPNTL hL hL1 hL2 hL3 u hau huM
  have hu : 0 < u := ha.trans_le hau
  have hM : 0 < M := ha.trans_le haM
  have hauL : a*L ≤ u*L :=
    mul_le_mul_of_nonneg_right hau hL.le
  have huML : u*L ≤ M*L :=
    mul_le_mul_of_nonneg_right huM hL.le
  have h1 : 1 ≤ u*L := by
    calc
      1 = a*(1/a) := by field_simp
      _ ≤ a*L := mul_le_mul_of_nonneg_left hL1 ha.le
      _ ≤ u*L := hauL
  have hsmall : h ≤ u*L := by
    calc
      h = a*(h/a) := by field_simp
      _ ≤ a*L := mul_le_mul_of_nonneg_left hL2 ha.le
      _ ≤ u*L := hauL
  have hscale : 4*(2*C+C*h+h) ≤ h*(u*L) := by
    calc
      4*(2*C+C*h+h) =
          (h*a)*(4*(2*C+C*h+h)/(h*a)) := by field_simp
      _ ≤ (h*a)*L :=
        mul_le_mul_of_nonneg_left hL3 (by positivity)
      _ = h*(a*L) := by ring
      _ ≤ h*(u*L) := mul_le_mul_of_nonneg_left hauL hh.le
  have hexp : Real.exp (a*L) ≤ Real.exp (u*L) :=
    Real.exp_le_exp.mpr hauL
  have hPNT' : ∀ t, Real.exp (u*L) ≤ t →
      |Green64Analytic.ReciprocalPrimeGrid.primeRemainder t| ≤
        C*t/(Real.log t)^2 := by
    intro t ht
    exact hPNTL t (hexp.trans ht)
  have hShort := source_prime_free_window_lower_of_pnt2
    (u*L) h C h1 hh hC hsmall hscale hPNT'
  have hCompare : h/(4*M*L) ≤ h/(4*(u*L)) := by
    have hd1 : 0 < 4*M*L := by positivity
    have hd2 : 0 < 4*(u*L) := by positivity
    apply (div_le_div_iff₀ hd1 hd2).2
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr huML)]
  exact hCompare.trans hShort



/- Exact source owner: SourceShiftTwoOriginalQ0Window.lean; original line 46. -/
theorem source_free_window_reciprocal_eq (ell h : ℝ) :
    (∑ p ∈ Finset.Ioc ⌊Real.exp ell⌋₊ ⌊Real.exp (ell+h)⌋₊,
         if p.Prime then (p:ℝ)⁻¹ else 0) =
    ∑ p ∈ sourceFreePrimeWindow ell h, (p:ℝ)⁻¹ := by
  simp [sourceFreePrimeWindow, Finset.sum_filter]


end Green64Analytic.SourceBlockSieve

end

end

