module

public import Green64.Library.Weights.Part056
public import Green64.Library.Weights.Part053
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part052
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part051
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.Part032
public import Green64.Library.Analysis.Estimates.Part010

@[expose] public section

/-!
# Analysis / Estimates / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalTrueFiveIndexRawFourCellC6Mellin -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14500000

/-- The ORIGINAL SOURCE03 signed RAW Fourier/Mellin C6 saving
for all FOUR true matched OUTPUT dyadic rectangles attached to
one original five-index moving GLOBAL cell pair, outside its OWN
circle major arc, including real prime bands, physical harmonic
atom probability and arbitrary complex endpoint coefficient
vectors. The C6 large denominator and scale bounds are derived
from arithmetic, no assumed local spectral cancellation. -/
theorem eventually_source_original_true_five_index_RAW_FOUR_CELL_mellin_C6_windows434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z)),
    let SA : z.1.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : z.1.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
    let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
      then bCoeff n else 0
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let Raw : ℕ → ℕ → ℂ := fun M N =>
      (-((-1:ℂ)^(z.1.1.card+z.1.2.card))) *
        (∑ n ∈ TA, ∑ mm ∈ TB,
          (if n∈(Finset.range M).image (fun i => M+i) then
            aCell n else 0) *
          (if mm∈(Finset.range N).image (fun i => N+i) then
            bCell mm else 0) *
          phase (n*mm))
    ‖Raw M0 N0‖^2 ≤ 125*(EA*EB)*L^(-Bsave) ∧
    ‖Raw M0 (2*N0)‖^2 ≤ 125*(EA*EB)*L^(-Bsave) ∧
    ‖Raw (2*M0) N0‖^2 ≤ 125*(EA*EB)*L^(-Bsave) ∧
    ‖Raw (2*M0) (2*N0)‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
  have hGeometry :=
    eventually_source_original_true_five_index_RAW_selected_CELL_mellin_window434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hGeometry] with L hGeometryL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep blockA blockB hDisjoint
    m Qchar hm hTbLower hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
  let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
  let aCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    then bCoeff n else 0
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    sourceOriginalPureMellinPhase434 ζ n
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let Raw : ℕ → ℕ → ℂ := fun M N =>
    (-((-1:ℂ)^(z.1.1.card+z.1.2.card))) *
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if n∈(Finset.range M).image (fun i => M+i) then
          aCell n else 0) *
        (if mm∈(Finset.range N).image (fun i => N+i) then
          bCell mm else 0) *
        phase (n*mm))
  have hWindow (M N : ℕ)
      (hMchoice : M=M0 ∨ M=2*M0)
      (hNchoice : N=N0 ∨ N=2*N0) :
      ‖Raw M N‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
    have hh := hGeometryL x Y Hprime d sep
      blockA blockB hDisjoint m Qchar hm hTbLower
      hAvar hBvar hhA hhB xi hxi z hz
      ζ aCoeff bCoeff M N hMchoice hNchoice theta k hk hOutside
    change ‖Raw M N‖^2 ≤ 125*(EA*EB)*L^(-Bsave) at hh
    exact hh
  exact ⟨hWindow M0 N0 (Or.inl rfl) (Or.inl rfl),
    hWindow M0 (2*N0) (Or.inl rfl) (Or.inr rfl),
    hWindow (2*M0) N0 (Or.inr rfl) (Or.inl rfl),
    hWindow (2*M0) (2*N0) (Or.inr rfl) (Or.inr rfl)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFullRawFourMatchedOwnMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- UNCONDITIONAL original SOURCE03 signed RAW Fourier/Mellin
minor bound on the FULL output integer-product atom supports
of one authentic ν/jA/χA/jB/χB, restricted by actual global
cell masks and outside its OWN moving major circle.
All FOUR true matched output dyad C6 estimates are derived
from the real arithmetic and glued by an exact four-window
output Fubini identity, losing factor 16 in squared norm,
but NO output-atom count, source prime-fibre cardinality,
or arbitrary analytical spectral assumption. Full output
inverse atom energies are used, preserving original laws. -/
theorem eventually_source_original_true_full_RAW_four_output_own_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z)),
    let SA : z.1.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : z.1.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
    let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
      then bCoeff n else 0
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    ‖(-((-1:ℂ)^(z.1.1.card+z.1.2.card))) *
      (∑ n∈TA, ∑ mm∈TB, aCell n*bCell mm*phase (n*mm))‖^2 ≤
      16*(125*(EA*EB)*L^(-Bsave)) := by
  have hFour :=
    eventually_source_original_true_five_index_RAW_FOUR_CELL_mellin_C6_windows434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hFour,eventually_ge_atTop (4:ℝ)]
    with L hFourL hL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep blockA blockB hDisjoint
    m Qchar hm hTbLower hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
  let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
  let aCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    then bCoeff n else 0
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    sourceOriginalPureMellinPhase434 ζ n
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let Raw : ℕ → ℕ → ℂ := fun M N =>
    (-((-1:ℂ)^(z.1.1.card+z.1.2.card))) *
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if n∈(Finset.range M).image (fun i => M+i) then
          aCell n else 0) *
        (if mm∈(Finset.range N).image (fun i => N+i) then
          bCell mm else 0) *
        phase (n*mm))

  let R : ℕ → ℕ → ℂ := fun M N =>
    ∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico M (2*M) then aCell n else 0) *
      (if mm∈Finset.Ico N (2*N) then bCell mm else 0) *
      phase (n*mm)
  let sigma : ℂ := -((-1:ℂ)^(z.1.1.card+z.1.2.card))
  obtain ⟨h00,h01,h10,h11⟩ := hFourL
    x Y Hprime d sep blockA blockB hDisjoint
    m Qchar hm hTbLower hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside
  have hRange (M N : ℕ) : R M N =
    ∑ n∈TA,∑ mm∈TB,
      (if n∈(Finset.range M).image (fun i=>M+i)
        then aCell n else 0) *
      (if mm∈(Finset.range N).image (fun j=>N+j)
        then bCell mm else 0) *
      phase (n*mm) := by
    exact source_original_finite_output_window_ico_range434
      TA TB aCell bCell (fun n mm => phase (n*mm)) M N
  have hSigned (M N : ℕ) : sigma*R M N = Raw M N := by
    dsimp only [Raw]
    exact congrArg (fun u : ℂ => sigma*u) (hRange M N)
  have hS00 : ‖sigma*R M0 N0‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
    rw [hSigned]; exact h00
  have hS01 : ‖sigma*R M0 (2*N0)‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
    rw [hSigned]; exact h01
  have hS10 : ‖sigma*R (2*M0) N0‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
    rw [hSigned]; exact h10
  have hS11 : ‖sigma*R (2*M0) (2*N0)‖^2 ≤
      125*(EA*EB)*L^(-Bsave) := by
    rw [hSigned]; exact h11
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hAprops := hhA z.1 hν
  have hBprops := hhB z.1 hν
  have hPrimeA : ∀ i p, p∈SA i → p.Prime :=
    fun i p hp => d.hTbPrime i.val.1 p hp
  have hPrimeB : ∀ i p, p∈SB i → p.Prime :=
    fun i p hp => d.hTbPrime i.val.1 p hp
  have hExact : (∑ n∈TA,∑ mm∈TB,
       aCell n*bCell mm*phase (n*mm)) =
      R M0 N0 + R M0 (2*N0) +
      R (2*M0) N0 + R (2*M0) (2*N0) := by
    have hh := source_original_true_RAW_four_selected_output_windows434
      SA SB hPrimeA hPrimeB (hAvar z.1) (hBvar z.1)
      hAprops.1 hBprops.1 hAprops.2 hBprops.2
      z.2.1.1 z.2.2.1 aCoeff bCoeff phase
    have h4M : 2*(2*M0) = 4*M0 := by omega
    have h4N : 2*(2*N0) = 4*N0 := by omega
    simpa only [R,h4M,h4N] using hh
  have hMuA : ∀ i p, p∈SA i → 0 ≤ muA i p := by
    intro i p hp
    exact div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg p))
      (cfg.hv.trans_le (d.hVbig i.val.1)).le
  have hMuB : ∀ i p, p∈SB i → 0 ≤ muB i p := by
    intro i p hp
    exact div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg p))
      (cfg.hv.trans_le (d.hVbig i.val.1)).le
  have hEA : 0 ≤ EA := by
    dsimp only [EA]
    exact Finset.sum_nonneg (fun n hn =>
      div_nonneg (sq_nonneg _)
        (source_original_physical_product_atom_nonneg434 SA muA hMuA n))
  have hEB : 0 ≤ EB := by
    dsimp only [EB]
    exact Finset.sum_nonneg (fun n hn =>
      div_nonneg (sq_nonneg _)
        (source_original_physical_product_atom_nonneg434 SB muB hMuB n))
  have hSave : 0 ≤ 125*(EA*EB)*L^(-Bsave) := by
    have hLp : 0 ≤ L := by linarith [hL]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hEA hEB))
      (Real.rpow_nonneg hLp _)
  exact source_original_finite_signed_four_window_operator434
    sigma (∑ n∈TA,∑ mm∈TB,aCell n*bCell mm*phase (n*mm))
    (R M0 N0) (R M0 (2*N0))
    (R (2*M0) N0) (R (2*M0) (2*N0))
    (125*(EA*EB)*L^(-Bsave)) hSave hExact
    hS00 hS01 hS10 hS11
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedFullFiveIndexOffOwnMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- REAL ORIGINAL SOURCE03 five-index (nu,jA,chiA,jB,chiB)
signed primitive-Knu MINUS signed RAW Fourier/Mellin
operator for full independently labelled BIG-prime laws,
arbitrary complex selected integer-output test vectors.
Outside this EXACT mode's moving own circle arc,
its physical squared-L2 saving follows from already checked
unconditional four-window Knu-C6 and four-window RAW-C6.
The former lives on true selected output GLOBAL log cells,
the latter is a masked full-support sum: their comparison
uses exact TRUE harmonic atom masses and finite selected
energy inclusion, not artificial atom-cardinality losses.
All real grouped prime interval and denominator conditions
are explicit. This is ONE five-index term, not yet the original
full all-nu/four-sign correlation or Green64. -/
theorem eventually_source_original_true_signed_full_five_index_off_own_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (JA JB : Finset ℤ) (massA massB : ℤ → ℝ)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
    let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
    let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
    let activeA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    let activeB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    let TA := TAfull.filter activeA
    let TB := TBfull.filter activeB
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ)*
      (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
    let phaseInput : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
      w v * sourceOriginalActualPrimitiveComparisonKernel434
        Qchar JA JB (hAvar z.1) (hBvar z.1)
        massA massB (DA v) nA (DB v) nB
        (z.1.1.card+z.1.2.card) * phaseInput v
    let Knu : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v)
    let phaseOutput : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let aCell : ℕ → ℂ := fun n =>
      if activeA n then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if activeB n then bCoeff n else 0
    let SignedRaw : ℂ :=
      -((-1:ℂ)^(z.1.1.card+z.1.2.card)) *
      (∑ nA∈TAfull, ∑ nB∈TBfull,
        aCell nA*bCell nB*phaseOutput (nA*nB))
    let EAfull : ℝ := ∑ n∈TAfull,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBfull : ℝ := ∑ n∈TBfull,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let EAsel : ℝ := ∑ n∈TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBsel : ℝ := ∑ n∈TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let BK : ℝ :=
      16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    ‖Knu-SignedRaw‖^2 ≤ 2*(BK+BR)*EAfull*EBfull := by
  have hKEvent :=
    eventually_source_original_true_Knu_FULL_four_matched_CELL_mellin_operator434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  have hREvent :=
    eventually_source_original_true_full_RAW_four_output_own_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hKEvent,hREvent,eventually_ge_atTop (4:ℝ)]
    with L hKL hRL hL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
  let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
  let activeA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
  let activeB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
  let TA := TAfull.filter activeA
  let TB := TBfull.filter activeB
  let X := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SA v.1
  let DB : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SB v.2
  let w : X → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ)*
    (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
  let phaseInput : X → ℂ := fun v =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((DA v*DB v:ℕ):ℤ)) *
    sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
  let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
    w v * sourceOriginalActualPrimitiveComparisonKernel434
      Qchar JA JB (hAvar z.1) (hBvar z.1)
      massA massB (DA v) nA (DB v) nB
      (z.1.1.card+z.1.2.card) * phaseInput v
  let Knu : ℂ := ∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v)
  let phaseOutput : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    sourceOriginalPureMellinPhase434 ζ n
  let aCell : ℕ → ℂ := fun n =>
    if activeA n then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if activeB n then bCoeff n else 0
  let SignedRaw : ℂ :=
    -((-1:ℂ)^(z.1.1.card+z.1.2.card)) *
    (∑ nA∈TAfull, ∑ nB∈TBfull,
      aCell nA*bCell nB*phaseOutput (nA*nB))
  let EAfull : ℝ := ∑ n∈TAfull,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EBfull : ℝ := ∑ n∈TBfull,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let EAsel : ℝ := ∑ n∈TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EBsel : ℝ := ∑ n∈TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let BK : ℝ :=
    16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave)))
  let BR : ℝ := 2000*L^(-Bsave)
  have hAtoms := source_original_true_nu_selected_atom_probability434
    cfg x L Y Hprime d hVbig m z.1.1 z.1.2
  have hPosA (n : ℕ) (hn : n∈TAfull) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n :=
    hAtoms.1 n hn
  have hPosB (n : ℕ) (hn : n∈TBfull) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n :=
    hAtoms.2.1 n hn
  have hBK : 0 ≤ BK := by
    dsimp only [BK]
    positivity
  have hBR : 0 ≤ BR := by
    dsimp only [BR]
    positivity
  have hK := hKL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  have hR := hRL x Y Hprime d sep
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside
  have hKnu : ‖Knu‖^2 ≤ BK*EAsel*EBsel := by
    dsimp only at hK
    convert hK using 1 <;> ring
  have hRaw : ‖SignedRaw‖^2 ≤ BR*EAfull*EBfull := by
    dsimp only at hR
    change ‖SignedRaw‖^2 ≤
      16*(125*(EAfull*EBfull)*L^(-Bsave)) at hR
    calc
      _ ≤ 16*(125*(EAfull*EBfull)*L^(-Bsave)) := hR
      _ = BR*EAfull*EBfull := by dsimp [BR]; ring
  have hKnuForCombine :
      ‖Knu‖^2 ≤ BK *
        (∑ n ∈ TAfull.filter activeA,
          ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n) *
        (∑ n ∈ TBfull.filter activeB,
          ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n) := by
    simpa only [EAsel, EBsel, TA, TB] using hKnu
  apply source_original_finite_selected_full_atom_signed_combine434
    TAfull TBfull activeA activeB
    (sourceOriginalPhysicalProductAtom434 SA muA)
    (sourceOriginalPhysicalProductAtom434 SB muB)
    hPosA hPosB aCoeff bCoeff Knu SignedRaw BK BR hBK hBR
  · convert hKnuForCombine using 1
    apply congrArg₂ (fun x y : ℝ => BK*x*y)
    · apply source_original_finite_filter_sum_decider_invariant434
    · apply source_original_finite_filter_sum_decider_invariant434
  · exact hRaw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedCanonicalFiveIndexOwnMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- REAL SOURCE03 signed primitive Knu-minus-RAW entire selected
jA/jB physical OUTPUT off-OWN-arc Fourier/Mellin minor with NO
externally postulated character/cell normalization assumptions.
All active primitive GLOBAL families JA/JB and their probability
masses nu_j are chosen CANONICALLY from the genuine ν-dependent
prime laws, with both lower xi thresholds and total<=1 proved
from full reciprocal-prime mass. The sharp atom energy and
five-index arithmetic C6 saving of RAW and Knu are inherited
unaltered. Still one original five-index, not full sh:correlation
or Green64, and source admissibility remains explicit. -/
theorem eventually_source_original_true_signed_canonical_five_index_off_own_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let JA := sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig z.1 (hAvar z.1) xi
    let JB := sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig z.1 (hBvar z.1) xi
    let massA := sourceOriginalProbeCellA434
      m d.Tb d.Vbig z.1 (hAvar z.1)
    let massB := sourceOriginalProbeCellB434
      m d.Tb d.Vbig z.1 (hBvar z.1)
    let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
    let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
    let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
    let activeA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    let activeB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    let TA := TAfull.filter activeA
    let TB := TBfull.filter activeB
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ)*
      (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
    let phaseInput : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
      w v * sourceOriginalActualPrimitiveComparisonKernel434
        Qchar JA JB (hAvar z.1) (hBvar z.1)
        massA massB (DA v) nA (DB v) nB
        (z.1.1.card+z.1.2.card) * phaseInput v
    let Knu : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v)
    let phaseOutput : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let aCell : ℕ → ℂ := fun n =>
      if activeA n then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if activeB n then bCoeff n else 0
    let SignedRaw : ℂ :=
      -((-1:ℂ)^(z.1.1.card+z.1.2.card)) *
      (∑ nA∈TAfull, ∑ nB∈TBfull,
        aCell nA*bCell nB*phaseOutput (nA*nB))
    let EAfull : ℝ := ∑ n∈TAfull,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBfull : ℝ := ∑ n∈TBfull,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let EAsel : ℝ := ∑ n∈TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBsel : ℝ := ∑ n∈TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let BK : ℝ :=
      16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    ‖Knu-SignedRaw‖^2 ≤ 2*(BK+BR)*EAfull*EBfull := by
  have hCore :=
    eventually_source_original_true_signed_full_five_index_off_own_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  classical
  let JA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig z.1 (hAvar z.1) xi
  let JB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig z.1 (hBvar z.1) xi
  let massA := sourceOriginalProbeCellA434
    m d.Tb d.Vbig z.1 (hAvar z.1)
  let massB := sourceOriginalProbeCellB434
    m d.Tb d.Vbig z.1 (hBvar z.1)
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hVpos (g : β) : 0 < d.Vbig g :=
    cfg.hv.trans_le (d.hVbig g)
  obtain ⟨hMassA,hMassB,hTotalA,hTotalB⟩ :=
    source_original_true_canonical_Knu_cell_mass_inputs434
      m z.1 d.Tb d.Vbig
      hVbig hVpos d.hTbPrime
      (hAvar z.1) (hBvar z.1) xi
      (hhA z.1 hν).1 (hhB z.1 hν).1 hxi
  have hBound := hCoreL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  simpa only [JA,JB,massA,massB] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedKernelOwnC6Minor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- UNCONDITIONAL original SOURCE03 five-index signed selected
two-integer Fourier/Mellin kernel C6 minor on its GENUINE OWN
moving rational circle complement. The fully canonical primitive
character families and active jA,jB probability masses are
derived from source data. The four-window RAW/Knu C6 estimate
is transferred to the LITERAL original
sourceOriginalProbeSignedSelectedFourierError434 by the
independently kernel-checked selected-atom signed Fubini identity.
Arbitrary complex selected coefficient tests retain their exact
inverse-harmonic-atom FULL support L2 norm, without any output
cardinality factor, synthetic joint H, or additional C6 premise.
ONE ν and selected output cell; not yet all-mode sh:correlation. -/
theorem eventually_source_original_true_SELECTED_kernel_five_index_off_own_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let JA := sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig z.1 (hAvar z.1) xi
    let JB := sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig z.1 (hBvar z.1) xi
    let massA := sourceOriginalProbeCellA434
      m d.Tb d.Vbig z.1 (hAvar z.1)
    let massB := sourceOriginalProbeCellB434
      m d.Tb d.Vbig z.1 (hBvar z.1)
    let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
    let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
    let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
    let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
    let activeA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    let activeB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    let TA := TAfull.filter activeA
    let TB := TBfull.filter activeB
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ)*
      (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
    let phaseInput : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
      w v * sourceOriginalActualPrimitiveComparisonKernel434
        Qchar JA JB (hAvar z.1) (hBvar z.1)
        massA massB (DA v) nA (DB v) nB
        (z.1.1.card+z.1.2.card) * phaseInput v
    let Knu : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v)
    let phaseOutput : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let aCell : ℕ → ℂ := fun n =>
      if activeA n then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if activeB n then bCoeff n else 0
    let SignedRaw : ℂ :=
      -((-1:ℂ)^(z.1.1.card+z.1.2.card)) *
      (∑ nA∈TAfull, ∑ nB∈TBfull,
        aCell nA*bCell nB*phaseOutput (nA*nB))
    let EAfull : ℝ := ∑ n∈TAfull,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBfull : ℝ := ∑ n∈TBfull,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let EAsel : ℝ := ∑ n∈TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EBsel : ℝ := ∑ n∈TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let BK : ℝ :=
      16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    ‖(∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ z.1 d.Tb d.Vbig
          Qchar (hAvar z.1) (hBvar z.1)
          xi ζ theta k nA nB)‖^2 ≤
      2*(BK+BR)*EAfull*EBfull := by
  have hSaved :=
    eventually_source_original_true_signed_canonical_five_index_off_own_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hSaved] with L hSavedL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  classical
  let JA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig z.1 (hAvar z.1) xi
  let JB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig z.1 (hBvar z.1) xi
  let massA := sourceOriginalProbeCellA434
    m d.Tb d.Vbig z.1 (hAvar z.1)
  let massB := sourceOriginalProbeCellB434
    m d.Tb d.Vbig z.1 (hBvar z.1)
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
  let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
  let activeA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
  let activeB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
  let TA := TAfull.filter activeA
  let TB := TBfull.filter activeB
  let EAfull : ℝ := ∑ n∈TAfull,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EBfull : ℝ := ∑ n∈TBfull,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let BK : ℝ :=
    16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave)))
  let BR : ℝ := 2000*L^(-Bsave)
  have hBound := hSavedL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  let X := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SA v.1
  let DB : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SB v.2
  let w : X → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ)*
    (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
  let phaseInput : X → ℂ := fun v =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((DA v*DB v:ℕ):ℤ)) *
    sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
  let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
    w v * sourceOriginalActualPrimitiveComparisonKernel434
      Qchar JA JB (hAvar z.1) (hBvar z.1)
      massA massB (DA v) nA (DB v) nB
      (z.1.1.card+z.1.2.card) * phaseInput v
  let Knu : ℂ := ∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v)
  let phaseOutput : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    sourceOriginalPureMellinPhase434 ζ n
  let aCell : ℕ → ℂ := fun n =>
    if activeA n then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if activeB n then bCoeff n else 0
  let SignedRaw : ℂ :=
    -((-1:ℂ)^(z.1.1.card+z.1.2.card)) *
    (∑ nA∈TAfull, ∑ nB∈TBfull,
      aCell nA*bCell nB*phaseOutput (nA*nB))
  have hFub := source_original_true_selected_cell_signed_fubini434
    J ell m hmJ z.1 d.Tb d.Vbig
    Qchar (hAvar z.1) (hBvar z.1)
    xi ζ theta k z.2.1.1 z.2.2.1 aCoeff bCoeff
  have hIdentity :
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ z.1 d.Tb d.Vbig
          Qchar (hAvar z.1) (hBvar z.1)
          xi ζ theta k nA nB) = Knu-SignedRaw := by
    convert hFub using 1
  have hBound' : ‖Knu-SignedRaw‖^2 ≤
      2*(BK+BR)*EAfull*EBfull := by
    simpa only [Knu,SignedRaw,BK,BR,EAfull,EBfull,
      JA,JB,massA,massB,SA,SB,muA,muB,TAfull,TBfull,TA,TB,
      activeA,activeB,X,DA,DB,w,phaseInput,F,phaseOutput,
      aCell,bCell] using hBound
  change ‖(∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ z.1 d.Tb d.Vbig
          Qchar (hAvar z.1) (hBvar z.1)
          xi ζ theta k nA nB)‖^2 ≤
      2*(BK+BR)*EAfull*EBfull
  rw [hIdentity]
  exact hBound'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalSelectedCellOwnC6Minor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine source03 physical free-mark signed RAW-minus-Knu C6
bound for the selected jB/jA original GLOBAL output cell,
outside the original five-index own moving circle arc.
The true selected two-integer joint kernel C6 arithmetic
is transported to arbitrary full source/target mark-sensitive
complex L2 endpoint tests with exact harmonic marginals.
No tensor-factorization, selected output count or spectral
hypothesis is introduced. Still ONE five-index selected
cell pair, not the global source03 sh:correlation. -/
theorem eventually_source_original_true_physical_selected_CELL_off_own_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z.1
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ z.1
        (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ z.1
        (fun g i => (v g i).val)
    let actB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    let actA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    let BK : ℝ := 16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
      (125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    let budget : ℝ := 2*(BK+BR)
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if actB (projS ab.1) ∧ actA (projT ab.2) then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ z.1 d.Tb d.Vbig Qchar
              (hAvar z.1) (hBvar z.1) xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
       budget *
         (∑ s : X, w s*‖sourceTest s‖^2) *
         (∑ v : X, w v*‖targetTest v‖^2) := by
  have hC6event :=
    eventually_source_original_true_SELECTED_kernel_five_index_off_own_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hC6event,eventually_ge_atTop (4:ℝ)]
    with L hC6L hL4
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    ζ theta k hk hOutside hWidth
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z.1
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ z.1
      (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ z.1
      (fun g i => (v g i).val)
  let actB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
  let actA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
  let SB : z.1.2 → Finset ℕ := fun q => d.Tb q.val.1
  let SA : z.1.1 → Finset ℕ := fun q => d.Tb q.val.1
  let muB : z.1.2 → ℕ → ℝ := fun q p =>
    (1/(p:ℝ))/(d.Vbig q.val.1)
  let muA : z.1.1 → ℕ → ℝ := fun q p =>
    (1/(p:ℝ))/(d.Vbig q.val.1)
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let BK : ℝ := 16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
    (125*L^(-Bsave)))
  let BR : ℝ := 2000*L^(-Bsave)
  let budget : ℝ := 2*(BK+BR)
  let H : ℕ → ℕ → ℂ := fun nB nA =>
    if actB nB ∧ actA nA then
      sourceOriginalProbeSignedSelectedFourierError434
        J ell m hmJ z.1 d.Tb d.Vbig Qchar
        (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB
    else 0
  have hBudgetNN : 0 ≤ budget := by
    dsimp only [budget,BK,BR]
    have hLpos : 0 < L := by linarith
    positivity
  have hSelected (bCoeff aCoeff : ℕ → ℂ) :
    ‖(∑ ij ∈ TB.product TA,
      bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2)‖^2 ≤
    budget*
      (∑ n∈TB, ‖bCoeff n‖^2 /
        sourceOriginalPhysicalProductAtom434 SB muB n) *
      (∑ n∈TA, ‖aCoeff n‖^2 /
        sourceOriginalPhysicalProductAtom434 SA muA n) := by
    have hh := hC6L
      x Y Hprime d sep hVbig blockA blockB hDisjoint
      m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi z hz
      ζ aCoeff bCoeff theta k hk hOutside hWidth
    dsimp only at hh
    have hSwap := source_original_finite_masked_two_sided_swap434
      TA TB actA actB aCoeff bCoeff
      (fun nA nB =>
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ z.1 d.Tb d.Vbig Qchar
          (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB)
    have hExact :
      (∑ ij ∈ TB.product TA,
        bCoeff ij.1*aCoeff ij.2*H ij.1 ij.2) =
      (∑ nA ∈ TA.filter actA,
        ∑ nB ∈ TB.filter actB,
          aCoeff nA*bCoeff nB*
            sourceOriginalProbeSignedSelectedFourierError434
              J ell m hmJ z.1 d.Tb d.Vbig Qchar
              (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB) := by
      calc
        _ = (∑ nB ∈ TB, ∑ nA ∈ TA,
          bCoeff nB*aCoeff nA*
            (if actB nB ∧ actA nA then
              sourceOriginalProbeSignedSelectedFourierError434
                J ell m hmJ z.1 d.Tb d.Vbig Qchar
                (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB
             else 0)) := by
               simp only [Finset.product_eq_sprod, Finset.sum_product]
               apply Finset.sum_congr rfl
               intro nB hnB
               apply Finset.sum_congr rfl
               intro nA hnA
               by_cases hc : actB nB ∧ actA nA
               · simp only [H, if_pos hc]
               · simp only [H, if_neg hc]
        _ = _ := by
          convert hSwap using 1
          apply Finset.sum_congr rfl
          intro nB hnB
          apply Finset.sum_congr rfl
          intro nA hnA
          by_cases hc : actB nB ∧ actA nA
          · simp [hc]
          · simp [hc]
          · exact source_original_finite_nested_filter_decider_invariant434
              TA TB actA actB _ _ _ _
              (fun nA nB =>
                aCoeff nA*bCoeff nB*
                  sourceOriginalProbeSignedSelectedFourierError434
                    J ell m hmJ z.1 d.Tb d.Vbig Qchar
                    (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB)
    rw [hExact]
    have hTarget :
      ‖(∑ nA ∈ TA.filter actA,
        ∑ nB ∈ TB.filter actB,
          aCoeff nA*bCoeff nB*
            sourceOriginalProbeSignedSelectedFourierError434
              J ell m hmJ z.1 d.Tb d.Vbig Qchar
              (hAvar z.1) (hBvar z.1) xi ζ theta k nA nB)‖^2 ≤
      budget *
        (∑ n∈TA, ‖aCoeff n‖^2 /
          sourceOriginalPhysicalProductAtom434 SA muA n) *
        (∑ n∈TB, ‖bCoeff n‖^2 /
          sourceOriginalPhysicalProductAtom434 SB muB n) := by
      simpa only [SA,SB,muA,muB,TA,TB,actA,actB,budget,BK,BR]
        using hh
    calc
      _ ≤ budget*
        (∑ n∈TA, ‖aCoeff n‖^2 /
          sourceOriginalPhysicalProductAtom434 SA muA n) *
        (∑ n∈TB, ‖bCoeff n‖^2 /
          sourceOriginalPhysicalProductAtom434 SB muB n) := hTarget
      _ = _ := by ring
  have hVpos (g : β) : 0 < d.Vbig g :=
    cfg.hv.trans_le (d.hVbig g)
  dsimp only
  intro sourceTest targetTest
  have hLift := source_original_true_physical_masked_signed_cell434
    J ell m hmJ z.1 d.Tb d.Vbig
    hVbig hVpos d.hTbPrime
    Qchar (hAvar z.1) (hBvar z.1) xi ζ theta k
    z.2.1.1 z.2.2.1 budget hBudgetNN
    hSelected sourceTest targetTest
  simpa only [BP,t,mu,X,w,projS,projT,actB,actA,budget]
    using hLift
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalSelectedCellOwnC6Power -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original SOURCE03 physical ν free-mark signed RAW-minus-Knu
OFF-OWN-CIRCLE selected GLOBAL pair minor operator estimate
with an EXPLICIT arbitrary L^-Bgoal logarithmic saving:
  ||signed masked physical||^2 <= 8000 L^-Bgoal Esource Etarget.
Both original harmonic prime-group laws, arbitrary complex
mark-sensitive endpoint tests, exact five-index moving arc
and C6 arithmetic are retained. Polynomial conductor/cell losses
are absorbed by the stated Bsave exponent inequality, not
ignored. Still one selected original ν/cell/character mode,
not the all-signs global sh:correlation or Green64. -/
theorem eventually_source_original_true_physical_selected_CELL_off_own_minor_log_saving434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar Cxi Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hExponentBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^Cxi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z.1
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ z.1
        (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ z.1
        (fun g i => (v g i).val)
    let actB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
    let actA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
    let BK : ℝ := 16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
      (125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    let budget : ℝ := 2*(BK+BR)
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if actB (projS ab.1) ∧ actA (projT ab.2) then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ z.1 d.Tb d.Vbig Qchar
              (hAvar z.1) (hBvar z.1) xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
       (8000*L^(-Bgoal)) *
         (∑ s : X, w s*‖sourceTest s‖^2) *
         (∑ v : X, w v*‖targetTest v‖^2) := by
  have hSaved :=
    eventually_source_original_true_physical_selected_CELL_off_own_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hSaved,eventually_ge_atTop (4:ℝ)]
    with L hSavedL hL4
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly z hz
    ζ theta k hk hOutside hWidth
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z.1
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ z.1
      (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ z.1
      (fun g i => (v g i).val)
  let actB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
  let actA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
  let BK : ℝ := 16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
    (125*L^(-Bsave)))
  let BR : ℝ := 2000*L^(-Bsave)
  let budget : ℝ := 2*(BK+BR)
  have hBudget :
      budget ≤ 8000*L^(-Bgoal) := by
    dsimp only [budget,BK,BR]
    exact source_original_true_physical_own_minor_budget434
      L (by linarith : 1 ≤ L) Qchar xi hxi
      Cchar Cxi Bsave Bgoal hCchar hCxi
      hQpoly hXipoly hExponentBudget
  have hVpos (g : β) : 0 < d.Vbig g :=
    cfg.hv.trans_le (d.hVbig g)
  have hw (s : X) : 0 ≤ w s := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun q : BP g => (q:ℕ)) (d.Vbig g) (hVpos g) p
  dsimp only
  intro sourceTest targetTest
  let ES : ℝ := ∑ s : X, w s*‖sourceTest s‖^2
  let ET : ℝ := ∑ v : X, w v*‖targetTest v‖^2
  have hES : 0 ≤ ES := by
    dsimp only [ES]
    exact Finset.sum_nonneg (fun s hs =>
      mul_nonneg (hw s) (sq_nonneg _))
  have hET : 0 ≤ ET := by
    dsimp only [ET]
    exact Finset.sum_nonneg (fun v hv =>
      mul_nonneg (hw v) (sq_nonneg _))
  have hOriginal := hSavedL
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower hAvar hBvar hhA hhB
    xi hxi z hz ζ theta k hk hOutside hWidth
    sourceTest targetTest
  have hScale :
      budget*ES*ET ≤ (8000*L^(-Bgoal))*ES*ET := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBudget hES) hET
  have hResult := hOriginal.trans hScale
  simpa only [BP,t,mu,X,w,projS,projT,actB,actA,
    ES,ET,budget,BK,BR] using hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueRetargetedCellPhysicalC6Power -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Genuine source03 full physical signed RAW-minus-Knu C6
on ANY ACTUAL active output jA/jB cell pair of a FIXED original
nu-pattern, using original primitive character/conductor
indices from ONE already existent true five-index z0.
No independent imaginary character is introduced: the
true expanded family membership of the retargeted z follows
from its actual product finite index family and both
canonical active cells. Per-cell log saving is uniform at
8000*L^-Bgoal with true full mark-sensitive physical L2 tests.
The present theorem does not yet globalize over all cells or nu. -/
theorem eventually_source_original_true_retargeted_cell_physical_own_C6_power434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar Cxi Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hExponentBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^Cxi)
    (z0 : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz0 : z0 ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (jA jB : ℤ)
    (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig z0.1 (hAvar z0.1) xi)
    (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig z0.1 (hBvar z0.1) xi)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar
              (⟨z0.1,((jA,z0.2.1.2),(jB,z0.2.2.2))⟩ :
                SourceOriginalTrueFiveIndex434 β m Qchar)))
    (hWidth : hAvar z0.1+hBvar z0.1 ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z0.1
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ z0.1
        (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ z0.1
        (fun g i => (v g i).val)
    let actB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z0.1) n=jB
    let actA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z0.1) n=jA
    let BK : ℝ := 16*((((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 *
      (125*L^(-Bsave)))
    let BR : ℝ := 2000*L^(-Bsave)
    let budget : ℝ := 2*(BK+BR)
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if actB (projS ab.1) ∧ actA (projT ab.2) then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ z0.1 d.Tb d.Vbig Qchar
              (hAvar z0.1) (hBvar z0.1) xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
       (8000*L^(-Bgoal)) *
         (∑ s : X, w s*‖sourceTest s‖^2) *
         (∑ v : X, w v*‖targetTest v‖^2) := by
  have hSaved :=
    eventually_source_original_true_physical_selected_CELL_off_own_minor_log_saving434
      cfg D Bsave hD C hExponent hSaving
      Cchar Cxi Bgoal hCchar hCxi hExponentBudget
      Aarc hAarc hArc
  filter_upwards [hSaved] with L hSavedL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    z0 hz0 jA jB hjA hjB ζ theta k hk hOutside hWidth
  let z : SourceOriginalTrueFiveIndex434 β m Qchar :=
    ⟨z0.1,((jA,z0.2.1.2),(jB,z0.2.2.2))⟩
  have hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi :=
    source_original_true_retarget_active_global_cell434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi
      z0 hz0 jA jB hjA hjB
  have hh := hSavedL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ
    hTbLower hAvar hBvar hhA hhB
    xi hxi hQpoly hXipoly z hz ζ theta k hk
    hOutside hWidth
  simpa only [z] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllActiveCellsPhysicalC6Power -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual source03 ν original free-prime-mark signed
RAW-minus-Knu Fourier/Mellin operator OFF THE OWN moving
rational arc OF EACH active source-B/target-A GLOBAL cell
has a global squared-L2 log-saving with only the CARDINALITY
of genuine attainable original log-cell pairs as a factor.
The true C6 selected two-integer arithmetic is kernel-verified,
and exact L2 physical full-mark pushforward is performed
before genuine finite GLOBAL-cell gluing. True primitive
characters are retargeted from ONE existing original z0.
No arbitrary hMinor premise, no fake common arc radius, no
extra cost for discarded original physical states.
This is ONE original nu; other nu/four sign modes and the
complete sh:correlation/Green64 remain outside its conclusion. -/
theorem eventually_source_original_true_ALL_active_cells_physical_own_C6_power434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar Cxi Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hExponentBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^Cxi)
    (z0 : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz0 : z0 ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hWidth : hAvar z0.1+hBvar z0.1 ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z0.1
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun v : z0.1.2 => d.Tb v.val.1) (hBvar z0.1)
    let CA := sourceOriginalCandidateLogCells434
      (fun v : z0.1.1 => d.Tb v.val.1) (hAvar z0.1)
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (hBvar z0.1)
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ z0.1
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (hAvar z0.1)
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ z0.1
          (fun g i => (v g i).val))
    let activeB := sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig z0.1 (hBvar z0.1) xi
    let activeA := sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig z0.1 (hAvar z0.1) xi
    let ownArc : ℤ × ℤ → Prop := fun ij =>
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc /
          (Real.exp ((ij.2:ℝ)*hAvar z0.1) *
           Real.exp ((ij.1:ℝ)*hBvar z0.1)))
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ z0.1 d.Tb d.Vbig Qchar
        (hAvar z0.1) (hBvar z0.1) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    let masked : X × X → ℂ := fun ab =>
      if idxS ab.1 ∈ activeB ∧ idxT ab.2 ∈ activeA ∧
           ¬ownArc (idxS ab.1,idxT ab.2)
      then err ab else 0
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          masked ab)‖^2 ≤
        ((CB.product CA).card:ℝ) *
        (8000*L^(-Bgoal)) *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2) := by
  have hCellEvent :=
    eventually_source_original_true_retargeted_cell_physical_own_C6_power434
      cfg D Bsave hD C hExponent hSaving
      Cchar Cxi Bgoal hCchar hCxi hExponentBudget
      Aarc hAarc hArc
  filter_upwards [hCellEvent,eventually_ge_atTop (4:ℝ)] with L hCellL hL4
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    z0 hz0 ζ theta k hk hWidth
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ z0.1
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun v : z0.1.2 => d.Tb v.val.1) (hBvar z0.1)
  let CA := sourceOriginalCandidateLogCells434
    (fun v : z0.1.1 => d.Tb v.val.1) (hAvar z0.1)
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (hBvar z0.1)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ z0.1
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (hAvar z0.1)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ z0.1
        (fun g i => (v g i).val))
  let activeB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig z0.1 (hBvar z0.1) xi
  let activeA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig z0.1 (hAvar z0.1) xi
  let ownArc : ℤ × ℤ → Prop := fun ij =>
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^cfg.Carc /
        (Real.exp ((ij.2:ℝ)*hAvar z0.1) *
         Real.exp ((ij.1:ℝ)*hBvar z0.1)))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ z0.1 d.Tb d.Vbig Qchar
      (hAvar z0.1) (hBvar z0.1) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let masked : X × X → ℂ := fun ab =>
    if idxS ab.1 ∈ activeB ∧ idxT ab.2 ∈ activeA ∧
         ¬ownArc (idxS ab.1,idxT ab.2)
    then err ab else 0
  let save : ℝ := 8000*L^(-Bgoal)
  let eps : ℝ := Real.sqrt save
  have hSaveNN : 0 ≤ save := by
    dsimp only [save]
    have hLp : 0 < L := by linarith
    positivity
  have hEps : eps^2 = save :=
    Real.sq_sqrt hSaveNN
  have hCoverS (s : X) : idxS s∈CB :=
    source_original_probe_true_source_GLOBAL_cell_covered434
      J ell m hmJ z0.1 d.Tb (hBvar z0.1) s
  have hCoverT (v : X) : idxT v∈CA :=
    source_original_probe_true_target_GLOBAL_cell_covered434
      J ell m hmJ z0.1 d.Tb (hAvar z0.1) v
  have hVpos (g : β) : 0 < d.Vbig g :=
    cfg.hv.trans_le (d.hVbig g)
  have hw (s : X) : 0 ≤ w s := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun q : BP g => (q:ℕ)) (d.Vbig g) (hVpos g) p
  dsimp only
  intro sourceTest targetTest
  have hEach (ij : ℤ × ℤ) (hij : ij∈CB.product CA)
      (ff gg : X → ℂ) :
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (ff ab.1)*gg ab.2*
          (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
           then masked ab else 0))‖^2 ≤
        eps^2*(∑ s : X, w s*‖ff s‖^2) *
              (∑ v : X, w v*‖gg v‖^2) := by
    let keep : Prop :=
      ij.1∈activeB ∧ ij.2∈activeA ∧ ¬ownArc ij
    have hMaskEq (ab : X × X) :
        (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
         then masked ab else 0) =
        (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
         then (if keep then err ab else 0) else 0) := by
      by_cases heq : idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
      · have hs := heq.1
        have ht := heq.2
        simp only [if_pos heq,masked,keep]
        simp only [hs,ht]
      · simp only [if_neg heq]
    by_cases hkeep : keep
    · rcases hkeep with ⟨hB,hA,hOff⟩
      have hKeep : keep := ⟨hB,hA,hOff⟩
      let z : SourceOriginalTrueFiveIndex434 β m Qchar :=
        ⟨z0.1,((ij.2,z0.2.1.2),(ij.1,z0.2.2.2))⟩
      have hOwnOff :
        (theta:AddCircle (1:ℝ)) ∉
          sourceCircleRationalArcs434
            (k.natAbs*Nat.ceil (L^(D+1)))
            (L^cfg.Carc / sourceOriginalProbeTrueHprime434
              m Qchar hAvar hBvar z) := by
        simpa only [ownArc,z,sourceOriginalProbeTrueHprime434]
          using hOff
      have hCell := hCellL x Y Hprime d sep hVbig
        blockA blockB hDisjoint m Qchar hm J ell hmJ
        hTbLower hAvar hBvar hhA hhB
        xi hxi hQpoly hXipoly z0 hz0
        ij.2 ij.1 hA hB
        ζ theta k hk hOwnOff hWidth ff gg
      have hSame :
        (∑ ab : X × X,
          ((w ab.1*w ab.2:ℝ):ℂ) *
            star (ff ab.1)*gg ab.2*
            (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
             then masked ab else 0)) =
        (∑ ab : X × X,
          ((w ab.1*w ab.2:ℝ):ℂ) *
            star (ff ab.1)*gg ab.2*
            (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
             then err ab else 0)) := by
        apply Finset.sum_congr rfl
        intro ab hab
        rw [hMaskEq ab]
        simp only [if_pos hKeep]
      rw [hSame]
      simpa only [eps,hEps,save,BP,t,mu,X,w,idxS,idxT,err]
        using hCell
    · have hZero (ab : X × X) :
        (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
         then masked ab else 0) = 0 := by
        rw [hMaskEq ab]
        by_cases hIdx : idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
        · simp [hIdx,hkeep]
        · simp [hIdx]
      have hES : 0 ≤ ∑ s : X, w s*‖ff s‖^2 :=
        Finset.sum_nonneg (fun s hs =>
          mul_nonneg (hw s) (sq_nonneg _))
      have hET : 0 ≤ ∑ v : X, w v*‖gg v‖^2 :=
        Finset.sum_nonneg (fun v hv =>
          mul_nonneg (hw v) (sq_nonneg _))
      have hh : 0 ≤ eps^2 *
          (∑ s : X, w s*‖ff s‖^2) *
          (∑ v : X, w v*‖gg v‖^2) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hES) hET
      have hSumZero :
          (∑ ab : X × X,
            ((w ab.1*w ab.2:ℝ):ℂ) *
              star (ff ab.1)*gg ab.2*
              (if idxS ab.1=ij.1 ∧ idxT ab.2=ij.2
               then masked ab else 0)) = 0 := by
        simp_rw [hZero]
        simp
      rw [hSumZero]
      simpa using hh
  have hGlobal := source_original_finite_dyad_operator_globalize434
    CB CA idxS idxT hCoverS hCoverT
    w w hw hw masked eps hEach sourceTest targetTest
  rw [hEps] at hGlobal
  simpa only [BP,t,mu,X,w,CB,CA,idxS,idxT,
    activeB,activeA,ownArc,err,masked,save] using hGlobal
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalActiveOffOwnMask -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The literal ORIGINAL SOURCE03 signed full-residual active
AND not-own-major GLOBAL mask, written with its actual
original source/target chosen free-prime slot embeddings,
is EQUIVALENT to the exact active off-own-cell mask used
in the proved true physical all-GLOBAL-C6 minor theorem.
No arithmetic, harmonic, or phase expression is replaced:
the source03 source-B / target-A selected prime products
are definitionally the corresponding original free products.
This is the precise outstanding Boolean-geometric interface
for final ν-level major/minor/bad fusion. -/
theorem source_original_true_physical_ACTIVE_OFF_OWN_iff434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi L D Carc ζ theta : ℝ) (k : ℤ)
    (s v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val)
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val)
    let idxB := sourceOriginalLiteralLogCellIndex434 hB XB
    let idxA := sourceOriginalLiteralLogCellIndex434 hA XA
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let arc :=
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/(Real.exp ((idxA:ℝ)*hA) *
                  Real.exp ((idxB:ℝ)*hB)))
    ((¬(sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2,
          ((s (sourceOriginalProbeSourceBFreeEmbedding434
              J ell m hmJ ν z).1
              (sourceOriginalProbeSourceBFreeEmbedding434
                J ell m hmJ ν z).2).val:ℕ)) ∉ activeB) ∧
      ¬(sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1,
          ((v (sourceOriginalProbeTargetAFreeEmbedding434
              J ell m hmJ ν z).1
              (sourceOriginalProbeTargetAFreeEmbedding434
                J ell m hmJ ν z).2).val:ℕ)) ∉ activeA)) ∧
      ¬(idxB∈activeB ∧ idxA∈activeA ∧ arc)) ↔
    idxB∈activeB ∧ idxA∈activeA ∧ ¬arc := by
  classical
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
    (fun g i => (s g i).val)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
    (fun g i => (v g i).val)
  let idxB := sourceOriginalLiteralLogCellIndex434 hB XB
  let idxA := sourceOriginalLiteralLogCellIndex434 hA XA
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let arc := (theta : AddCircle (1:ℝ)) ∈
    sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^Carc/(Real.exp ((idxA:ℝ)*hA) *
                Real.exp ((idxB:ℝ)*hB)))
  change (¬(idxB ∉ activeB) ∧ ¬(idxA ∉ activeA)) ∧
      ¬(idxB∈activeB ∧ idxA∈activeA ∧ arc) ↔
    idxB∈activeB ∧ idxA∈activeA ∧ ¬arc
  simp only [not_not]
  tauto
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteEquivalentPhysicalMasks -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal finite weighted complex bilinear invariance under
LOGICALLY EQUIVALENT original active/off-own physical masks.
The two Boolean tests may have DIFFERENT Lean DecidableProp
instances, and the joint H(x,y) may be completely coupled.
Exactly the full source/target complex tests and real weights
are retained; no atom pushforward or analytic bound assumed. -/
theorem source_original_finite_equiv_physical_masks434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wx : X → ℝ) (wy : Y → ℝ)
    (f : X → ℂ) (g : Y → ℂ)
    (H : X × Y → ℂ)
    (P Q : X × Y → Prop)
    (hPQ : ∀ xy, P xy ↔ Q xy) :
    (∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) *
      star (f xy.1)*g xy.2 *
        (if P xy then H xy else 0)) =
    (∑ xy : X × Y,
      ((wx xy.1*wy xy.2:ℝ):ℂ) *
      star (f xy.1)*g xy.2 *
        (if Q xy then H xy else 0)) := by
  classical
  apply Finset.sum_congr rfl
  intro xy hxy
  by_cases hp : P xy
  · have hq : Q xy := (hPQ xy).mp hp
    simp only [if_pos hp, if_pos hq]
  · have hq : ¬Q xy := fun hh => hp ((hPQ xy).mpr hh)
    simp only [if_neg hp, if_neg hq]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAnyNuAllActiveC6Power -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The true SOURCE03 full physical ν signed RAW-minus-Knu
C6 minor over ALL active source-B/target-A GLOBAL output
cell pairs, with no imaginary assumption of an existing
primitive five-index mode. When both original active
cell sets are nonempty, the TRUE primitive level-one
character produces a legitimate five-index in the
original expanded family. If either is empty, the
entire active physical operator is LITERALLY zero.
The result holds for EVERY original ν pattern, Qchar>=1.
Only actual original source group arithmetic/Dirichlet
parameter hypotheses remain, not a fake hMode premise. -/
theorem eventually_source_original_true_ANY_nu_ALL_active_physical_C6_power434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar Cxi Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hExponentBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^Cxi)
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m)
    (hQpositive : 0 < Qchar)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hWidth : hAvar ν+hBvar ν ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun v : ν.2 => d.Tb v.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun v : ν.1 => d.Tb v.val.1) (hAvar ν)
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (hBvar ν)
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (hAvar ν)
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let activeB := sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig ν (hBvar ν) xi
    let activeA := sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig ν (hAvar ν) xi
    let ownArc : ℤ × ℤ → Prop := fun ij =>
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc /
          (Real.exp ((ij.2:ℝ)*hAvar ν) *
           Real.exp ((ij.1:ℝ)*hBvar ν)))
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν d.Tb d.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    let masked : X × X → ℂ := fun ab =>
      if idxS ab.1 ∈ activeB ∧ idxT ab.2 ∈ activeA ∧
           ¬ownArc (idxS ab.1,idxT ab.2)
      then err ab else 0
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          masked ab)‖^2 ≤
        ((CB.product CA).card:ℝ) *
        (8000*L^(-Bgoal)) *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2) := by
  have hOld :=
    eventually_source_original_true_ALL_active_cells_physical_own_C6_power434
      cfg D Bsave hD C hExponent hSaving
      Cchar Cxi Bgoal hCchar hCxi hExponentBudget
      Aarc hAarc hArc
  filter_upwards [hOld,eventually_ge_atTop (4:ℝ)]
    with L hOldL hL4
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive ζ theta k hk hWidth
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun v : ν.2 => d.Tb v.val.1) (hBvar ν)
  let CA := sourceOriginalCandidateLogCells434
    (fun v : ν.1 => d.Tb v.val.1) (hAvar ν)
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (hBvar ν)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (hAvar ν)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let activeB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig ν (hBvar ν) xi
  let activeA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig ν (hAvar ν) xi
  let ownArc : ℤ × ℤ → Prop := fun ij =>
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^cfg.Carc /
        (Real.exp ((ij.2:ℝ)*hAvar ν) *
         Real.exp ((ij.1:ℝ)*hBvar ν)))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Qchar
      (hAvar ν) (hBvar ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let masked : X × X → ℂ := fun ab =>
    if idxS ab.1 ∈ activeB ∧ idxT ab.2 ∈ activeA ∧
         ¬ownArc (idxS ab.1,idxT ab.2)
    then err ab else 0
  by_cases hBoth : activeA.Nonempty ∧ activeB.Nonempty
  · obtain ⟨z0,hzν,hz0⟩ :=
      source_original_true_active_cells_have_actual_mode434
        blockA blockB m Qchar hQpositive d.Tb d.Vbig
        hAvar hBvar xi ν hν hBoth.1 hBoth.2
    subst ν
    have hWidth0 : hAvar z0.1+hBvar z0.1 ≤ 1 := hWidth
    have hFrom := hOldL x Y Hprime d sep hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ
      hTbLower hAvar hBvar hhA hhB xi hxi
      hQpoly hXipoly z0 hz0
      ζ theta k hk hWidth0
    dsimp only
    intro sourceTest targetTest
    have hh := hFrom sourceTest targetTest
    simpa only [BP,t,mu,X,w,CB,CA,idxS,idxT,
      activeB,activeA,ownArc,err,masked] using hh
  · have hNoActive (ab : X × X) :
        ¬(idxS ab.1∈activeB ∧ idxT ab.2∈activeA ∧
          ¬ownArc (idxS ab.1,idxT ab.2)) := by
      intro hmem
      apply hBoth
      exact ⟨⟨idxT ab.2,hmem.2.1⟩,
        ⟨idxS ab.1,hmem.1⟩⟩
    have hZero (ab : X × X) : masked ab = 0 := by
      dsimp only [masked]
      exact if_neg (hNoActive ab)
    have hVpos (g : β) : 0 < d.Vbig g :=
      cfg.hv.trans_le (d.hVbig g)
    have hw (s : X) : 0 ≤ w s := by
      apply source_original_variable_BIG_mass_nonneg434 BP t mu
      intro g p
      exact source_original_harmonic_prime_nonneg434
        (fun q : BP g => (q:ℕ)) (d.Vbig g) (hVpos g) p
    dsimp only
    intro sourceTest targetTest
    have hZeroSum :
        (∑ ab : X × X,
          ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*masked ab) = 0 := by
      apply Finset.sum_eq_zero
      intro ab hab
      rw [hZero ab]
      ring
    have hES : 0 ≤ ∑ s : X, w s*‖sourceTest s‖^2 :=
      Finset.sum_nonneg (fun s hs =>
        mul_nonneg (hw s) (sq_nonneg _))
    have hET : 0 ≤ ∑ v : X, w v*‖targetTest v‖^2 :=
      Finset.sum_nonneg (fun v hv =>
        mul_nonneg (hw v) (sq_nonneg _))
    have hCoeff : 0 ≤ ((CB.product CA).card:ℝ) *
        (8000*L^(-Bgoal)) := by
      have hLpos : 0 < L := by linarith
      positivity
    have hBound := mul_nonneg (mul_nonneg hCoeff hES) hET
    change
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
            masked ab)‖^2 ≤
        ((CB.product CA).card:ℝ) *
          (8000*L^(-Bgoal)) *
          (∑ s : X, w s*‖sourceTest s‖^2) *
          (∑ v : X, w v*‖targetTest v‖^2)
    rw [hZeroSum]
    simpa using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAnyNuExactGluerMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- UNCONDITIONAL true original source03 ν physical SIGNED
RAW-minus-Knu all-active OFF-OWN-CIRCLE C6 minor estimate,
written using the EXACT literal active AND NOT major mask
of SourceOriginalTrueFullResidualFromOwnMinor434, including
original product over SOURCE-B/TARGET-A free-mark embeddings.
The full original source03 physical harmonic law and BOTH
arbitrary mark-sensitive complex tests are preserved.
The ENTIRE analytically challenging C6 hMinor is here proved,
not postulated: its exact cost is Nν*8000 L^-Bgoal.
Original other major C191 conditions and all ν/four signs
global integration remain separate. -/
theorem eventually_source_original_true_ANY_nu_PHYSICAL_gluer_exact_hMinor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar Cxi Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxi : 0 ≤ Cxi)
    (hExponentBudget : Bgoal+8*(Cchar+Cxi) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^Cxi)
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hQpositive : 0 < Qchar)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hWidth : hAvar ν+hBvar ν ≤ 1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun v : ν.2 => d.Tb v.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun v : ν.1 => d.Tb v.val.1) (hAvar ν)
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (hBvar ν)
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (hAvar ν)
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let activeB := sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig ν (hBvar ν) xi
    let activeA := sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig ν (hAvar ν) xi
    let ownArc : ℤ × ℤ → Prop := fun ij =>
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc /
          (Real.exp ((ij.2:ℝ)*hAvar ν) *
           Real.exp ((ij.1:ℝ)*hBvar ν)))
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν d.Tb d.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    let originalMask : X × X → Prop := fun ab =>
      (¬(sourceOriginalLiteralLogCellIndex434 (hBvar ν)
        (∏ j : ν.2,
          ((ab.1 (sourceOriginalProbeSourceBFreeEmbedding434
             J ell m hmJ ν j).1
             (sourceOriginalProbeSourceBFreeEmbedding434
              J ell m hmJ ν j).2).val:ℕ)) ∉ activeB) ∧
       ¬(sourceOriginalLiteralLogCellIndex434 (hAvar ν)
        (∏ j : ν.1,
          ((ab.2 (sourceOriginalProbeTargetAFreeEmbedding434
             J ell m hmJ ν j).1
             (sourceOriginalProbeTargetAFreeEmbedding434
              J ell m hmJ ν j).2).val:ℕ)) ∉ activeA)) ∧
      ¬(idxS ab.1∈activeB ∧ idxT ab.2∈activeA ∧
          ownArc (idxS ab.1,idxT ab.2))
    let masked : X × X → ℂ := fun ab =>
      if originalMask ab then err ab else 0
    ∀ sourceTest targetTest : X → ℂ,
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          masked ab)‖^2 ≤
        ((CB.product CA).card:ℝ) *
        (8000*L^(-Bgoal)) *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2) := by
  have hMinorEvent :=
    eventually_source_original_true_ANY_nu_ALL_active_physical_C6_power434
      cfg D Bsave hD C hExponent hSaving
      Cchar Cxi Bgoal hCchar hCxi hExponentBudget
      Aarc hAarc hArc
  filter_upwards [hMinorEvent] with L hMinorL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig blockA blockB hDisjoint
    m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive ζ theta k hk hWidth
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun v : ν.2 => d.Tb v.val.1) (hBvar ν)
  let CA := sourceOriginalCandidateLogCells434
    (fun v : ν.1 => d.Tb v.val.1) (hAvar ν)
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (hBvar ν)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (hAvar ν)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let activeB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig ν (hBvar ν) xi
  let activeA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig ν (hAvar ν) xi
  let ownArc : ℤ × ℤ → Prop := fun ij =>
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^cfg.Carc /
        (Real.exp ((ij.2:ℝ)*hAvar ν) *
         Real.exp ((ij.1:ℝ)*hBvar ν)))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Qchar
      (hAvar ν) (hBvar ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let originalMask : X × X → Prop := fun ab =>
      (¬(sourceOriginalLiteralLogCellIndex434 (hBvar ν)
        (∏ j : ν.2,
          ((ab.1 (sourceOriginalProbeSourceBFreeEmbedding434
             J ell m hmJ ν j).1
             (sourceOriginalProbeSourceBFreeEmbedding434
              J ell m hmJ ν j).2).val:ℕ)) ∉ activeB) ∧
       ¬(sourceOriginalLiteralLogCellIndex434 (hAvar ν)
        (∏ j : ν.1,
          ((ab.2 (sourceOriginalProbeTargetAFreeEmbedding434
             J ell m hmJ ν j).1
             (sourceOriginalProbeTargetAFreeEmbedding434
              J ell m hmJ ν j).2).val:ℕ)) ∉ activeA)) ∧
      ¬(idxS ab.1∈activeB ∧ idxT ab.2∈activeA ∧
          ownArc (idxS ab.1,idxT ab.2))
  let activeMinor : X × X → Prop := fun ab =>
    idxS ab.1∈activeB ∧ idxT ab.2∈activeA ∧
      ¬ownArc (idxS ab.1,idxT ab.2)
  let masked : X × X → ℂ := fun ab =>
    if originalMask ab then err ab else 0
  let maskedOriginal : X × X → ℂ := fun ab =>
    if activeMinor ab then err ab else 0
  have hLogical (ab : X × X) :
      originalMask ab ↔ activeMinor ab := by
    exact source_original_true_physical_ACTIVE_OFF_OWN_iff434
      J ell m hmJ ν d.Tb d.Vbig Qchar
      (hAvar ν) (hBvar ν) xi L D cfg.Carc
      ζ theta k ab.1 ab.2
  have hMin := hMinorL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ
    hTbLower hAvar hBvar hhA hhB xi hxi
    hQpoly hXipoly ν hν hQpositive ζ theta k hk hWidth
  dsimp only
  intro sourceTest targetTest
  have hEq := source_original_finite_equiv_physical_masks434
    w w sourceTest targetTest err originalMask activeMinor hLogical
  have hOrig :
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        masked ab)‖^2 =
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        maskedOriginal ab)‖^2 := by
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hp : originalMask ab
    · have hq : activeMinor ab := (hLogical ab).mp hp
      simp only [masked,maskedOriginal,if_pos hp,if_pos hq]
    · have hq : ¬activeMinor ab := fun h => hp ((hLogical ab).mpr h)
      simp only [masked,maskedOriginal,if_neg hp,if_neg hq]
  rw [hOrig]
  simpa only [BP,t,mu,X,w,CB,CA,idxS,idxT,activeB,
    activeA,ownArc,err,maskedOriginal,activeMinor] using
      (hMin sourceTest targetTest)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAnyNuFullSignedC191C6 -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- ORIGINAL SOURCE03 complete ν physical RAW-minus-canonical-Knu
signed Fourier/Mellin residual from REAL original C191 major,
the now UNCONDITIONALLY proven ALL-ACTIVE off-own C6 minor,
and the original rare discarded GLOBAL event paid ONCE.
Both arithmetic C191 prime bands/mesh and the true C6
Dirichlet group-separation/source interval assumptions
remain EXPLICIT in the theorem (NOT analytic hMinor).
For arbitrary mark-sensitive physical source/target L2 tests,
  squared norm <=2*(2*(eps_C191²+Nν*8000L^-Bgoal)+Cgeo)*ES*ET
where Nν is the exact original attainable GLOBAL-cell-pair count.
This is ONE original ν, not yet four signs/all ν sh:correlation,
and no claim about T/Green64 prime mass. -/
theorem eventually_source_original_true_ANY_nu_full_physical_signed_C191_C6_434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBIGA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p)
    (hBIGB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p)
    (hL : 192 ≤ L)
    (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hXiNat : xi⁻¹ ≤ L^CxiNat)
    (iA : ν.1) (iB : ν.2)
    (uA vA uB vB : ℕ)
    (huA : 1 ≤ uA) (huB : 1 ≤ uB)
    (huvA : uA ≤ vA) (huvB : uB ≤ vB)
    (hvA : (vA:ℝ) ≤ Real.exp (L^d))
    (hvB : (vB:ℝ) ≤ Real.exp (L^d))
    (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
    (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
    (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
    (hYA : Y ≤ ((uA+1:ℕ):ℝ))
    (hYB : Y ≤ ((uB+1:ℕ):ℝ))
    (hBandA : data.Tb iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
    (hBandB : data.Tb iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hWidth : hAvar ν + hBvar ν ≤
      L^(-(Bmaj+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hAvar ν + hBvar ν ≤ 1)
    (hZeta : |ζ| ≤ L^C4),
    let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g p => p.val) data.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
      (hAvar ν) +
      ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν data.Tb data.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
       ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*err ab)‖^2 ≤
      2*(2*(eps^2+
        ((CB.product CA).card:ℝ)*(8000*L^(-Bgoal)))+Cgeo) *
        (∑ s : X,w s*‖sourceTest s‖^2) *
        (∑ v : X,w v*‖targetTest v‖^2) := by
  obtain ⟨K,Y,hK,hGlue⟩ :=
    source_original_true_full_signed_residual_from_own_minor_L2_434
      Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
  refine ⟨K,Y,hK,?_⟩
  have hMinorEvent :=
    eventually_source_original_true_ANY_nu_PHYSICAL_gluer_exact_hMinor434
      cfg D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc
  filter_upwards [hMinorEvent] with L hMinorL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data sep hVbig
    blockA blockB hDisjoint m Qchar hm
    J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBIGA hBIGB
    hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXiNat
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k hk S hS hSscale
    hQchar hBudget hC4 hDeltaLe hWidth hWidth1 hZeta
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) data.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
    (hAvar ν) +
    ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
  let minorBudget : ℝ :=
    ((CB.product CA).card:ℝ)*(8000*L^(-Bgoal))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν data.Tb data.Vbig Qchar
      (hAvar ν) (hBvar ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  have hhPosA : 0 < hAvar ν := (hhA ν hν).1
  have hhPosB : 0 < hBvar ν := (hhB ν hν).1
  have hMinor := hMinorL x Ydata Hprime data sep hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ
      hTbLower hAvar hBvar hhA hhB xi hxi
      hQpoly hXipoly ν hν hQpositive ζ theta k hk hWidth1
  dsimp only
  intro sourceTest targetTest
  have hMinVal := hMinor sourceTest targetTest
  have hResult := hGlue J ell m hmJ ν data.Tb data.Vbig hVbig
      Vmin hVmin hMass Qchar hBIGA hBIGB
      (hAvar ν) (hBvar ν) xi hhPosA hhPosB hxi
      L hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXiNat
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB
      hBandA hBandB ζ theta k D cfg.Carc
      S hS hSscale hQchar hBudget
      hC4 hDeltaLe hWidth hWidth1 hZeta
      minorBudget sourceTest targetTest
      (by simpa only [BP,t,mu,X,w,CB,CA,minorBudget] using hMinVal)
  simpa only [BP,t,mu,X,w,CB,CA,eps,Cgeo,err,
      minorBudget] using hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAnyNuUniformMeshFull -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- ORIGINAL SOURCE03 full physical ν signed RAW-minus-Knu
residual with all REAL arithmetic C191 major / C6 minor /
single discounted GLOBAL bad event proved, AND the actual
canonical uniform Mellin mesh and retained-cell schedule
used to ABSORB both the genuine ν-cell-pair count and Cgeo.
Its entire coefficient is <=
  2*(2*(eps_C191²+72000 L^-Bout)+L^(-2 Bmaj)).
The original K,Y constants and all prime-band validity,
source grouping and true physical free-mark measures remain
explicit. No analytic hMinor or synthetic cell-cardinality
input; no full all-pattern/four-sign correlation claimed. -/
theorem eventually_source_original_true_ANY_nu_uniform_mesh_FULL_signed_C191_C6_434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBIGA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p)
    (hBIGB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p)
    (hL : 192 ≤ L)
    (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hXiNat : xi⁻¹ ≤ L^CxiNat)
    (iA : ν.1) (iB : ν.2)
    (uA vA uB vB : ℕ)
    (huA : 1 ≤ uA) (huB : 1 ≤ uB)
    (huvA : uA ≤ vA) (huvB : uB ≤ vB)
    (hvA : (vA:ℝ) ≤ Real.exp (L^d))
    (hvB : (vB:ℝ) ≤ Real.exp (L^d))
    (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
    (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
    (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
    (hYA : Y ≤ ((uA+1:ℕ):ℝ))
    (hYB : Y ≤ ((uB+1:ℕ):ℝ))
    (hBandA : data.Tb iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
    (hBandB : data.Tb iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hWidth : hAvar ν + hBvar ν ≤
      L^(-(Bmaj+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hAvar ν + hBvar ν ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount :
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA :
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB :
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1))),
    let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g p => p.val) data.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
      (hAvar ν) +
      ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν data.Tb data.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
       ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*err ab)‖^2 ≤
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) *
        (∑ s : X,w s*‖sourceTest s‖^2) *
        (∑ v : X,w v*‖targetTest v‖^2) := by
  obtain ⟨K,Y,hK,hFull⟩ :=
    eventually_source_original_true_ANY_nu_full_physical_signed_C191_C6_434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hFull] with L hFullL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data sep hVbig
    blockA blockB hDisjoint m Qchar hm
    J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBIGA hBIGB
    hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXiNat
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k hk S hS hSscale
    hQchar hBudget hC4 hDeltaLe hWidth hWidth1 hZeta
    hLMesh hCount hMeshA hMeshB hXiChoice
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) data.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
    (hAvar ν) +
    ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν data.Tb data.Vbig Qchar
      (hAvar ν) (hBvar ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  have hCoeff := source_original_true_uniform_mesh_ACTUAL_nu_budget434
    m ν data.Tb Cq C4 CxiNat
    L Bmaj d M Bout Bgoal eps hBmaj.le hd hM hLMesh hCount
    hPrimeUpperA hPrimeUpperB hXiExponent hMinorExponent
  have hCoeffReal :
      2*(2*(eps^2+((CB.product CA).card:ℝ)*
          (8000*L^(-Bgoal)))+Cgeo) ≤
        2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) := by
    simpa only [CB,CA,Cgeo,eps,hMeshA,hMeshB,hXiChoice] using hCoeff
  have hVpos : ∀ g : β, 0 < data.Vbig g :=
    fun g => hVmin.trans_le (hMass g)
  have hw (s : X) : 0 ≤ w s := by
    apply source_original_variable_BIG_mass_nonneg434 BP t mu
    intro g p
    exact source_original_harmonic_prime_nonneg434
      (fun q : BP g => (q:ℕ)) (data.Vbig g) (hVpos g) p
  dsimp only
  intro sourceTest targetTest
  let ES : ℝ := ∑ s : X,w s*‖sourceTest s‖^2
  let ET : ℝ := ∑ v : X,w v*‖targetTest v‖^2
  have hES : 0 ≤ ES := Finset.sum_nonneg
    (fun s hs => mul_nonneg (hw s) (sq_nonneg _))
  have hET : 0 ≤ ET := Finset.sum_nonneg
    (fun v hv => mul_nonneg (hw v) (sq_nonneg _))
  have hMain := hFullL x Ydata Hprime data sep hVbig
    blockA blockB hDisjoint m Qchar hm
    J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBIGA hBIGB
    hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXiNat
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k hk S hS hSscale
    hQchar hBudget hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  have hScale :
      (2*(2*(eps^2+((CB.product CA).card:ℝ)*
          (8000*L^(-Bgoal)))+Cgeo))*ES*ET ≤
        (2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))))*ES*ET := by
    apply mul_le_mul_of_nonneg_right _ hET
    exact mul_le_mul_of_nonneg_right hCoeffReal hES
  have hOriginal :
      ‖(∑ ab : X × X,
       ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*err ab)‖^2 ≤
        (2*(2*(eps^2+((CB.product CA).card:ℝ)*
          (8000*L^(-Bgoal)))+Cgeo))*ES*ET := by
    simpa only [BP,t,mu,X,w,CB,CA,eps,Cgeo,err,ES,ET] using hMain
  have hResult := hOriginal.trans hScale
  simpa only [BP,t,mu,X,w,eps,err,ES,ET] using hResult
end Green64Analytic.CorrelationSquare

end

