module

public import Green64.Library.Correlation.Part040
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Correlation.Part036
public import Green64.Library.Correlation.Part037
public import Green64.Library.Correlation.Part039
public import Green64.Library.Weights.Part023
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part015
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Green64.Library.Weights.Part047
public import Green64.Library.Correlation.Part034
public import Green64.Library.Sieve.Foundations.Part004
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Weights / Part051

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalTrueFiveIndexPrimitiveMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- One TRUE original source03 five-index primitive
comparison Fourier mode: ν,jA,χA,jB,χB, exact
-(-1)^(|A|+|B|) sign and two χ(X)/ν_j coefficients,
two fully marked independent BIG prime products and
the original -kθ physical phase. Individual squared
saving pays the EXACT cell coefficient νA⁻¹νB⁻¹,
not a global Q⁴xi⁻² surrogate. Valid off the
TRUE pair-dependent rational major arcs.
The unshared output products XA,XB remain explicit
physical output inputs; no coupling to raw marks is
claimed by this one-mode Fourier bound. -/
theorem eventually_source_original_true_five_index_primitive_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D) (C : ℕ)
    (hExponent : cfg.C0*Real.log
      (((cfg.tmax.factorial:ℕ):ℝ)*
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
      (hVbig : ∀ g : β, d.Vbig g =
        ∑ p ∈ d.Tb g,1/(p:ℝ))
      (blockA blockB : Finset β)
      (hDisjoint : Disjoint blockA blockB)
      (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
        Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hA hB : SourceOriginalProbePattern434 β m → ℝ)
      (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hA ν ∧ hA ν ≤ 1)
      (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
        blockA blockB m, 0 < hB ν ∧ hB ν ≤ 1)
      (xi : ℝ) (hxi : 0 < xi)
      (z : Σ ν : SourceOriginalProbePattern434 β m,
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) ×
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))))
      (hz : z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar d.Tb d.Vbig hA hB xi)
      (baseA : SourceOriginalGramPrimeTuple434
        (fun t : z.1.1 => d.Tb t.val.1) → ℂ)
      (baseB : SourceOriginalGramPrimeTuple434
        (fun t : z.1.2 => d.Tb t.val.1) → ℂ)
      (hbA : ∀ v, ‖baseA v‖ ≤ 1)
      (hbB : ∀ v, ‖baseB v‖ ≤ 1)
      (XA XB : ℕ)
      (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
      (hOutside : (theta:AddCircle (1:ℝ)) ∉
         sourceCircleRationalArcs434
           (k.natAbs*Nat.ceil (L^(D+1)))
           (L^cfg.Carc/
             sourceOriginalProbeTrueHprime434 m Qchar hA hB z)),
      let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
      let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
      let muA : z.1.1 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let muB : z.1.2 → ℕ → ℝ :=
        fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
      let pa := sourceOriginalGramPrimeProduct434 SA
      let pb := sourceOriginalGramPrimeProduct434 SB
      let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
      let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
      let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
        fun a => baseA a*
          sourceOriginalPrimitiveInputCellMode434
            Qchar (hA z.1) z.2.1.1 z.2.1.2 (pa a)
      let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
        fun b => baseB b*
          sourceOriginalPrimitiveInputCellMode434
            Qchar (hB z.1) z.2.2.1 z.2.2.2 (pb b)
      let oA : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
        Qchar (hA z.1) (sourceOriginalProbeCellA434
          m d.Tb d.Vbig z.1 (hA z.1))
        z.2.1.1 z.2.1.2 XA
      let oB : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
        Qchar (hB z.1) (sourceOriginalProbeCellB434
          m d.Tb d.Vbig z.1 (hB z.1))
        z.2.2.1 z.2.2.2 XB
      let coeff : ℂ := -((-1:ℂ)^(z.1.1.card+z.1.2.card))*oA*oB
      let cost : ℝ :=
        sourceOriginalProbeExpandedCost434
          m Qchar d.Tb d.Vbig hA hB z
      ‖coeff * sourceOriginalFiniteTwoSidedMinorBilinear434
        wa wb fA fB (fun q => Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))‖^2 ≤
        cost^2*(2000*L^(-Bsave)) := by
  have hUnit :=
    eventually_source_original_true_five_index_unit_cell_minor434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hUnit,eventually_ge_atTop (1:ℝ)]
    with L hBound hL
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower hA hB
    hhA hhB xi hxi z hz baseA baseB hbA hbB XA XB
    theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let cA := z.2.1.2
  let cB := z.2.2.2
  let modeA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => baseA a * star
      (cA.2 (pa a : ZMod (cA.1.val+1)))
  let modeB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => baseB b * star
      (cB.2 (pb b : ZMod (cB.1.val+1)))
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => baseA a *
      sourceOriginalPrimitiveInputCellMode434
        Qchar (hA z.1) z.2.1.1 cA (pa a)
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => baseB b *
      sourceOriginalPrimitiveInputCellMode434
        Qchar (hB z.1) z.2.2.1 cB (pb b)
  let oA : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
    Qchar (hA z.1) (sourceOriginalProbeCellA434
      m d.Tb d.Vbig z.1 (hA z.1)) z.2.1.1 cA XA
  let oB : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
    Qchar (hB z.1) (sourceOriginalProbeCellB434
      m d.Tb d.Vbig z.1 (hB z.1)) z.2.2.1 cB XB
  let coeff : ℂ := -((-1:ℂ)^(z.1.1.card+z.1.2.card))*oA*oB
  let cost : ℝ :=
    sourceOriginalProbeExpandedCost434
      m Qchar d.Tb d.Vbig hA hB z
  let I : ℂ := sourceOriginalFiniteTwoSidedMinorBilinear434
    wa wb fA fB (fun q => Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hProduct := Finset.mem_product.mp
    (Finset.mem_sigma.mp hz).2
  have hjA : z.2.1.1 ∈ sourceOriginalProbeActiveCellsA434
      m d.Tb d.Vbig z.1 (hA z.1) xi :=
    (Finset.mem_product.mp hProduct.1).1
  have hjB : z.2.2.1 ∈ sourceOriginalProbeActiveCellsB434
      m d.Tb d.Vbig z.1 (hB z.1) xi :=
    (Finset.mem_product.mp hProduct.2).1
  have hMassA : 0 < sourceOriginalProbeCellA434
      m d.Tb d.Vbig z.1 (hA z.1) z.2.1.1 :=
    hxi.trans_le ((source_original_probe_active_cell_A_mem_iff434
      m d.Tb d.Vbig z.1 (hA z.1) xi
      (hhA z.1 hν).1 hxi _).mp hjA)
  have hMassB : 0 < sourceOriginalProbeCellB434
      m d.Tb d.Vbig z.1 (hB z.1) z.2.2.1 :=
    hxi.trans_le ((source_original_probe_active_cell_B_mem_iff434
      m d.Tb d.Vbig z.1 (hB z.1) xi
      (hhB z.1 hν).1 hxi _).mp hjB)
  have hCoeff :=
    source_original_signed_primitive_output_pair_norm434
      Qchar (z.1.1.card+z.1.2.card)
      (hA z.1) (hB z.1)
      (sourceOriginalProbeCellA434 m d.Tb d.Vbig z.1 (hA z.1))
      (sourceOriginalProbeCellB434 m d.Tb d.Vbig z.1 (hB z.1))
      z.2.1.1 z.2.2.1 cA cB XA XB hMassA hMassB
  have hCoeffBound : ‖coeff‖ ≤ cost := by
    simpa only [coeff,cost,oA,oB,
      sourceOriginalProbeExpandedCost434,
      sourceOriginalTwoCellCoefficient434]
      using hCoeff
  have hModeA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖modeA v‖ ≤ 1 := by
    have hChi : ‖star (cA.2 (pa v : ZMod (cA.1.val+1)))‖ ≤ 1 := by
      simpa only [norm_star] using cA.2.norm_le_one _
    dsimp [modeA]
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 :=
        mul_le_mul (hbA v) hChi
          (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hModeB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖modeB v‖ ≤ 1 := by
    have hChi : ‖star (cB.2 (pb v : ZMod (cB.1.val+1)))‖ ≤ 1 := by
      simpa only [norm_star] using cB.2.norm_le_one _
    dsimp [modeB]
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 :=
        mul_le_mul (hbB v) hChi
          (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hI := hBound x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hA hB hhA hhB xi z hz modeA modeB
    hModeA hModeB theta k hk hOutside
  have hInputA (v : SourceOriginalGramPrimeTuple434 SA) :
      (if sourceOriginalLiteralLogCell434
        (hA z.1) z.2.1.1 (pa v) then modeA v else 0) =
      fA v := by
    dsimp [fA,modeA,sourceOriginalPrimitiveInputCellMode434]
    split_ifs <;> ring
  have hInputB (v : SourceOriginalGramPrimeTuple434 SB) :
      (if sourceOriginalLiteralLogCell434
        (hB z.1) z.2.2.1 (pb v) then modeB v else 0) =
      fB v := by
    dsimp [fB,modeB,sourceOriginalPrimitiveInputCellMode434]
    split_ifs <;> ring
  have hInputAeq : (fun v => if sourceOriginalLiteralLogCell434
    (hA z.1) z.2.1.1 (pa v) then modeA v else 0) = fA :=
    funext hInputA
  have hInputBeq : (fun v => if sourceOriginalLiteralLogCell434
    (hB z.1) z.2.2.1 (pb v) then modeB v else 0) = fB :=
    funext hInputB
  dsimp only at hI
  rw [hInputAeq,hInputBeq] at hI
  change ‖I‖^2 ≤ 2000*L^(-Bsave) at hI
  have hCostSq : ‖coeff‖^2 ≤ cost^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCoeffBound 2
  have hSaveNonneg : 0 ≤ 2000*L^(-Bsave) := by
    have hLp : 0 ≤ L := by linarith
    positivity
  have hCombined :
      ‖coeff‖^2*‖I‖^2 ≤ cost^2*(2000*L^(-Bsave)) :=
    mul_le_mul hCostSq hI (sq_nonneg _) (sq_nonneg _)
  change ‖coeff * I‖^2 ≤ cost^2*(2000*L^(-Bsave))
  calc
    _ = ‖coeff‖^2*‖I‖^2 := by rw [norm_mul,mul_pow]
    _ ≤ cost^2*(2000*L^(-Bsave)) := hCombined
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueExpandedSignedPhysicalTerm -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- EXACT type of the original source03 probe ν,
two active GLOBAL cell indices and two genuine
primitive Dirichlet character indices. -/
abbrev SourceOriginalTrueFiveIndex434
    (G : Type) (m Q : ℕ) :=
  Σ ν : SourceOriginalProbePattern434 G m,
    (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
    (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)))

/-- An actual single SOURCE03 signed primitive Fourier
bilinear mode, not a synthetic arbitrary indexed term.
The A/B physical prime tuple laws and cell masks
are constructed from genuine d.Tb and d.Vbig groups,
with full ν-dependent mark-sensitive endpoint tests.
Both output χ(X)/ν_j factors, source sign, and the
true -k*theta phase appear unchanged. -/
noncomputable def sourceOriginalTrueExpandedSignedPhysicalTerm434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434}
    {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (z : SourceOriginalTrueFiveIndex434 G m Q)
    (baseA : SourceOriginalGramPrimeTuple434
      (fun t : z.1.1 => d.Tb t.val.1) → ℂ)
    (baseB : SourceOriginalGramPrimeTuple434
      (fun t : z.1.2 => d.Tb t.val.1) → ℂ)
    (XA XB : ℕ) (theta : ℝ) (k : ℤ) : ℂ :=
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wb : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => baseA a*sourceOriginalPrimitiveInputCellMode434
      Q (hA z.1) z.2.1.1 z.2.1.2 (pa a)
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => baseB b*sourceOriginalPrimitiveInputCellMode434
      Q (hB z.1) z.2.2.1 z.2.2.2 (pb b)
  let oA : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
    Q (hA z.1) (sourceOriginalProbeCellA434
      m d.Tb d.Vbig z.1 (hA z.1)) z.2.1.1 z.2.1.2 XA
  let oB : ℂ := sourceOriginalPrimitiveOutputCellCoefficient434
    Q (hB z.1) (sourceOriginalProbeCellB434
      m d.Tb d.Vbig z.1 (hB z.1)) z.2.2.1 z.2.2.2 XB
  let coeff : ℂ := -((-1:ℂ)^(z.1.1.card+z.1.2.card))*oA*oB
  coeff*sourceOriginalFiniteTwoSidedMinorBilinear434
    wa wb fA fB
    (fun q => Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (((pa q.1*pb q.2:ℕ):ℤ)))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMovingUnionReducedDir -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Exact arithmetic interface between TRUE source03
moving circle arcs and the genuine physical Fourier
frequency -k*theta. Membership in the UNION chooses
SOME original five-index mode z, not every mode.
A true rational h/q is lifted, multiplied by -k,
and reduced to a COPRIME u'/q' with q'<=|k| *ceil(L^(D+1)).
The phase e(-k*theta*Dprod) is exactly the original
rational ZMod additive character e_q'(u'*Dprod)
times the REAL beta remainder e(beta*Dprod),
and beta meets the actual mode-Hcell Dirichlet scale.
The budget S is an EXPLICIT hypothesis: deriving it
polynomially and proving the true retained major
operator cancellation are separate tasks. -/
theorem source_original_true_moving_union_reduced_dir434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Qchar : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi L D Carc : ℝ) (k : ℤ) (theta : ℝ)
    (S : ℝ) (Dprod : ℕ)
    (hL : 0 ≤ L)
    (hBudget :
      ((k.natAbs*Nat.ceil (L^(D+1)) : ℕ):ℝ) *
        |(k:ℝ)| * L^Carc ≤ 2*S)
    (hMajor : (theta : AddCircle (1:ℝ)) ∈
      sourceOriginalTrueMovingMajorUnion434
        blockA blockB m Qchar P V hA hB xi L D Carc k) :
    ∃ z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar P V hA hB xi,
      ∃ beta : ℝ, ∃ q' : ℕ, ∃ hq' : 0 < q',
      ∃ u' : ℤ, ∃ Nshift : ℤ,
        q' ≤ k.natAbs*Nat.ceil (L^(D+1)) ∧
        Nat.Coprime u'.natAbs q' ∧
        -(k:ℝ)*theta =
          (u':ℝ)/(q':ℝ)+beta-(Nshift:ℝ) ∧
        |beta| *
          sourceOriginalProbeTrueHprime434
            m Qchar hA hB z ≤ 2*S/(q':ℝ) ∧
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (Dprod:ℤ) =
          sourceOriginalPositiveRationalPhaseAtNat434
            q' hq' u' Dprod *
          Green64SourceC6.integerPhase beta (Dprod:ℤ) := by
  classical
  let Qtheta : ℕ := k.natAbs*Nat.ceil (L^(D+1))
  obtain ⟨z,hz,q,hq,hqQ,h,hh,n,beta,hBeta,hFrequency⟩ :=
    source_original_true_moving_union_frequency_real_lift434
      blockA blockB m Qchar P V hA hB
      xi L D Carc k theta hMajor
  obtain ⟨q',hq',u',hqq',hCoprime,hRat,hFourier⟩ :=
    source_original_true_reduced_integer_frequency_phase434
      theta beta k (-(k*(h:ℤ))) (k*n) q Dprod hq
      hFrequency
  have hReducedLift :
      -(k:ℝ)*theta =
        (u':ℝ)/(q':ℝ)+beta-((k*n:ℤ):ℝ) := by
    rw [hRat]
    exact hFrequency
  have hQ' : q' ≤ Qtheta := hqq'.trans hqQ
  let Hcell : ℝ :=
    sourceOriginalProbeTrueHprime434 m Qchar hA hB z
  have hHpos : 0 < Hcell := by
    dsimp [Hcell,sourceOriginalProbeTrueHprime434]
    positivity
  have hBetaH :
      |beta| *Hcell ≤ |(k:ℝ)| *L^Carc := by
    calc
      _ ≤ (|(k:ℝ)| *(L^Carc/Hcell))*Hcell :=
        mul_le_mul_of_nonneg_right hBeta hHpos.le
      _ = |(k:ℝ)| *L^Carc := by
        field_simp [ne_of_gt hHpos]
  have hRightNN :
      0 ≤ |(k:ℝ)| *L^Carc :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL _)
  have hQle : (q':ℝ) ≤ (Qtheta:ℝ) := by
    exact_mod_cast hQ'
  have hqpos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  have hScale :
      |beta| *Hcell ≤ 2*S/(q':ℝ) := by
    apply (le_div_iff₀ hqpos).mpr
    calc
      (|beta| *Hcell)*(q':ℝ) ≤
          (|(k:ℝ)| *L^Carc)*(q':ℝ) :=
        mul_le_mul_of_nonneg_right hBetaH hqpos.le
      _ ≤ (|(k:ℝ)| *L^Carc)*(Qtheta:ℝ) :=
        mul_le_mul_of_nonneg_left hQle hRightNN
      _ = (Qtheta:ℝ)*|(k:ℝ)| *L^Carc := by ring
      _ ≤ 2*S := hBudget
  exact ⟨z,hz,beta,q',hq',u',k*n,
    hQ',hCoprime,hReducedLift,hScale,hFourier⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueGlobalPairReducedDyadC196Dir -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ORIGINAL source03 GLOBAL source-B/target-A pair (jB,jA)
has its own exact rational circle major arc. This version
does not require choosing a primitive Dirichlet character
to manufacture a five-index witness. The pair has its OWN rational
major arc. For THIS pair (not an arbitrary witness from the union), the exact -k*theta Fourier frequency has a reduced
coprime rational center and satisfies C196's dyadic Dirichlet
scale for EVERY pair U*V <= 3*Hcell. The physical Hcell=exp(jA*hA)exp(jB*hB), exact Fourier
frequency, and original integer phase are kept unchanged.
The polynomial S and Qchar budgets remain explicit. -/
theorem source_original_true_global_pair_reduced_dyad_C196_dir434
    (Qchar : ℕ) (hA hB : ℝ) (jA jB : ℤ)
    (L D Carc : ℝ) (k : ℤ) (theta S : ℝ) (Dprod : ℕ)
    (hL : 0 ≤ L)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^Carc ≤ 2*S)
    (hOwn : (theta:AddCircle (1:ℝ)) ∈
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB)))) :
    ∃ beta : ℝ, ∃ q' : ℕ, ∃ hq' : 0 < q',
      ∃ u' : ℤ, ∃ Nshift : ℤ,
        q' ≤ Qchar ∧ Nat.Coprime u'.natAbs q' ∧
        -(k:ℝ)*theta =
          (u':ℝ)/(q':ℝ)+beta-(Nshift:ℝ) ∧
        (∀ Uscale Vscale : ℝ,
          Uscale*Vscale ≤
            3*(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB)) →
          |beta| * (Uscale*Vscale) ≤ 2*S/(q':ℝ)) ∧
        Green64SourceC6.integerPhase (-(k:ℝ)*theta) (Dprod:ℤ) =
          sourceOriginalPositiveRationalPhaseAtNat434
            q' hq' u' Dprod *
          Green64SourceC6.integerPhase beta (Dprod:ℤ) := by
  classical
  let Qtheta : ℕ := k.natAbs*Nat.ceil (L^(D+1))
  let Hcell : ℝ := (Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB))
  have hHpos : 0 < Hcell := by
    dsimp [Hcell]
    positivity
  obtain ⟨q,hq,hqQ,h,hh,n,beta,hBeta,hFrequency⟩ :=
    source_circle_rational_arc_frequency_real_lift434
      Qtheta theta (L^Carc/Hcell) k hOwn
  obtain ⟨q',hq',u',hqq',hCoprime,hRat,hFourier⟩ :=
    source_original_true_reduced_integer_frequency_phase434
      theta beta k (-(k*(h:ℤ))) (k*n) q Dprod hq
      hFrequency
  have hReducedLift :
      -(k:ℝ)*theta =
        (u':ℝ)/(q':ℝ)+beta-((k*n:ℤ):ℝ) := by
    rw [hRat]
    exact hFrequency
  have hQ' : q' ≤ Qtheta := hqq'.trans hqQ
  have hQfinal : q' ≤ Qchar := hQ'.trans hQchar
  have hBetaH :
      |beta| *Hcell ≤ |(k:ℝ)| *L^Carc := by
    calc
      _ ≤ (|(k:ℝ)| *(L^Carc/Hcell))*Hcell :=
        mul_le_mul_of_nonneg_right hBeta hHpos.le
      _ = |(k:ℝ)| *L^Carc := by
        field_simp [ne_of_gt hHpos]
  have hBudget0 :
      (Qtheta:ℝ)*|(k:ℝ)| *L^Carc ≤ 2*(S/3) := by
    dsimp only [Qtheta]
    nlinarith [hBudget]
  have hRightNN : 0 ≤ |(k:ℝ)| *L^Carc :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL _)
  have hQle : (q':ℝ) ≤ (Qtheta:ℝ) := by
    exact_mod_cast hQ'
  have hqpos : (0:ℝ) < (q':ℝ) := by
    exact_mod_cast hq'
  have hScale :
      |beta| *Hcell ≤ 2*(S/3)/(q':ℝ) := by
    apply (le_div_iff₀ hqpos).mpr
    calc
      (|beta| *Hcell)*(q':ℝ) ≤
        (|(k:ℝ)| *L^Carc)*(q':ℝ) :=
          mul_le_mul_of_nonneg_right hBetaH hqpos.le
      _ ≤ (|(k:ℝ)| *L^Carc)*(Qtheta:ℝ) :=
          mul_le_mul_of_nonneg_left hQle hRightNN
      _ = (Qtheta:ℝ)*|(k:ℝ)| *L^Carc := by ring
      _ ≤ 2*(S/3) := hBudget0
  refine ⟨beta,q',hq',u',k*n,
    hQfinal,hCoprime,hReducedLift,?_,hFourier⟩
  intro Uscale Vscale hUV
  change Uscale*Vscale ≤ 3*Hcell at hUV
  have hScaled :
      |beta| *(Uscale*Vscale) ≤ |beta| *(3*Hcell) :=
    mul_le_mul_of_nonneg_left hUV (abs_nonneg _)
  have hScalar :
      3*(2*(S/3)/(q':ℝ)) = 2*S/(q':ℝ) := by ring
  calc
    |beta| *(Uscale*Vscale) ≤ |beta| *(3*Hcell) := hScaled
    _ = 3*(|beta| *Hcell) := by ring
    _ ≤ 3*(2*(S/3)/(q':ℝ)) :=
      mul_le_mul_of_nonneg_left hScale (by norm_num)
    _ = 2*S/(q':ℝ) := hScalar
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuPrimitiveCellMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- A TRUE original source03 primitive-character mode in
one retained A-block GLOBAL log cell, at an original target
prime product X_A. The input prime-product character uses
its actual primitive conductor; no fake product-only test. -/
noncomputable def sourceOriginalNuPrimitiveACellMode434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (h : ℝ) (j : ℤ) (Qchar : ℕ)
    (c : sourceOriginalPrimitiveFamily434 Qchar)
    (X : ℕ)
    (v : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  if sourceOriginalLiteralLogCell434 h j
       (sourceOriginalGramPrimeProduct434 S v) ∧
     sourceOriginalLiteralLogCell434 h j X
  then star (c.val.2
    ((sourceOriginalGramPrimeProduct434 S v:ℕ) :
      ZMod (c.val.1.val+1)))
  else 0
/-- Each physical primitive-character/cell mode is
pointwise bounded by one, including primes at which the
character vanishes. No hypothesis concerning independence
of a mark-dependent test is needed. -/
theorem source_original_nu_primitive_A_cell_mode_norm434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (h : ℝ) (j : ℤ) (Qchar : ℕ)
    (c : sourceOriginalPrimitiveFamily434 Qchar)
    (X : ℕ)
    (v : SourceOriginalGramPrimeTuple434 S) :
    ‖sourceOriginalNuPrimitiveACellMode434
        S h j Qchar c X v‖ ≤ 1 := by
  classical
  unfold sourceOriginalNuPrimitiveACellMode434
  split_ifs with hg
  · rw [norm_star]
    exact c.val.2.norm_le_one _
  · simp

/-- SAME SOURCE03 physical primitive B-block mode, with
actual B prime-label tuple and actual endpoint X_B. -/
noncomputable def sourceOriginalNuPrimitiveBCellMode434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (h : ℝ) (j : ℤ) (Qchar : ℕ)
    (c : sourceOriginalPrimitiveFamily434 Qchar)
    (X : ℕ)
    (v : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  sourceOriginalNuPrimitiveACellMode434 S h j Qchar c X v
/-- TRUE original ν-selected BIG/BIG physical C6 minor
circle estimate for an ACTUAL global primitive-character/
cell mode from each block. The marked functions are the
real source03 chi(D)*cell test; the physical terminal
products X_A,X_B are those of the supplied A/B tuples.
This is a genuine analytic specialization of the same
C6 physical integer minor theorem, not a new assumed
coefficient cancellation theorem. -/
theorem source_original_source03_true_nu_primitive_cell_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (cA cB : sourceOriginalPrimitiveFamily434 Qchar)
    (hA hB : ℝ) (jA jB : ℤ)
    (vA : SourceOriginalGramPrimeTuple434
       (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
       (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hrCap : (r:ℝ) ≤ L^cfg.Carc)
    (hDyadA :
      ((sourceOriginalGramPrimeProduct434
        (fun z : A => d.Tb z.val.1) vA:ℕ):ℝ) ≤ 2*(M:ℝ))
    (hDyadB :
      ((sourceOriginalGramPrimeProduct434
        (fun z : B => d.Tb z.val.1) vB:ℕ):ℝ) ≤ 2*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      sourceOriginalNuPrimitiveACellMode434 SA
        hA jA Qchar cA
        (sourceOriginalGramPrimeProduct434 SA vA)
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      sourceOriginalNuPrimitiveBCellMode434 SB
        hB jB Qchar cB
        (sourceOriginalGramPrimeProduct434 SB vB)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ tA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA tA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA tA:ℂ)*fA tA*
        (∑ tB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB tB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB tB:ℂ)*fB tB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA tA *
                  sourceOriginalGramPrimeProduct434 SB tB):ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤ 125*L^(-Bsave) := by
  obtain ⟨L0,hMinor⟩ :=
    source_original_source03_eventually_true_nu_fourier_minor434
      cfg D Bsave hD C hExponent hSaving
  refine ⟨L0,?_⟩
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern
    Qchar cA cB hA hB jA jB vA vB
    M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hrCap hDyadA hDyadB
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    sourceOriginalNuPrimitiveACellMode434 SA hA jA Qchar cA
      (sourceOriginalGramPrimeProduct434 SA vA)
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    sourceOriginalNuPrimitiveBCellMode434 SB hB jB Qchar cB
      (sourceOriginalGramPrimeProduct434 SB vB)
  have hfA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖fA v‖ ≤ 1 :=
    source_original_nu_primitive_A_cell_mode_norm434 SA
      hA jA Qchar cA _ v
  have hfB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖fB v‖ ≤ 1 :=
    source_original_nu_primitive_A_cell_mode_norm434 SB
      hB jB Qchar cB _ v
  have hBound := hMinor L hL x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern fA fB
    hfA hfB vA vB M N P Q hM hN a r beta0 theta k
    hApprox hr hcop hbeta hP hQ hR hrCap hDyadA hDyadB
  simpa only [SA,SB,fA,fB,sourceOriginalNuPrimitiveBCellMode434]
    using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuArbitraryMinorMode -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Exact original source03 ν BIG/BIG minor estimate for
any primitive input-cell character mode multiplied by
arbitrary mark-dependent complex tests of norm <=1.
The two tests are not assumed to depend only on their
prime products. All actual harmonic and window structures
and the original denominator restrictions are retained. -/
theorem source_original_source03_true_nu_arbitrary_test_cell_mode_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (cA cB : Σ q : Fin Qchar,
         DirichletCharacter ℂ (q.val+1))
    (hA hB : ℝ) (jA jB : ℤ)
    (bA : SourceOriginalGramPrimeTuple434
        (fun z : A => d.Tb z.val.1) → ℂ)
    (bB : SourceOriginalGramPrimeTuple434
        (fun z : B => d.Tb z.val.1) → ℂ)
    (hbA : ∀ v, ‖bA v‖ ≤ 1)
    (hbB : ∀ v, ‖bB v‖ ≤ 1)
    (vA : SourceOriginalGramPrimeTuple434
       (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
       (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hrCap : (r:ℝ) ≤ L^cfg.Carc)
    (hDyadA :
      ((sourceOriginalGramPrimeProduct434
        (fun z : A => d.Tb z.val.1) vA:ℕ):ℝ) ≤ 2*(M:ℝ))
    (hDyadB :
      ((sourceOriginalGramPrimeProduct434
        (fun z : B => d.Tb z.val.1) vB:ℕ):ℝ) ≤ 2*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => bA v * sourceOriginalPrimitiveInputCellMode434
        Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => bB v * sourceOriginalPrimitiveInputCellMode434
        Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ tA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA tA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA tA:ℂ)*fA tA*
        (∑ tB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB tB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB tB:ℂ)*fB tB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA tA *
                  sourceOriginalGramPrimeProduct434 SB tB):ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤ 125*L^(-Bsave) := by
  obtain ⟨L0,hMinor⟩ :=
    source_original_source03_eventually_true_nu_fourier_minor434
      cfg D Bsave hD C hExponent hSaving
  refine ⟨L0,?_⟩
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern
    Qchar cA cB hA hB jA jB bA bB hbA hbB vA vB
    M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hrCap hDyadA hDyadB
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => bA v * sourceOriginalPrimitiveInputCellMode434
      Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => bB v * sourceOriginalPrimitiveInputCellMode434
      Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)
  have hNormA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖sourceOriginalPrimitiveInputCellMode434 Qchar hA jA cA
        (sourceOriginalGramPrimeProduct434 SA v)‖ ≤ 1 := by
    unfold sourceOriginalPrimitiveInputCellMode434
    split_ifs
    · rw [norm_star]
      exact cA.2.norm_le_one _
    · simp
  have hNormB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖sourceOriginalPrimitiveInputCellMode434 Qchar hB jB cB
        (sourceOriginalGramPrimeProduct434 SB v)‖ ≤ 1 := by
    unfold sourceOriginalPrimitiveInputCellMode434
    split_ifs
    · rw [norm_star]
      exact cB.2.norm_le_one _
    · simp
  have hfA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖fA v‖ ≤ 1 := by
    change ‖bA v * sourceOriginalPrimitiveInputCellMode434
      Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)‖ ≤ 1
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 :=
        mul_le_mul (hbA v) (hNormA v)
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hfB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖fB v‖ ≤ 1 := by
    change ‖bB v * sourceOriginalPrimitiveInputCellMode434
      Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)‖ ≤ 1
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 :=
        mul_le_mul (hbB v) (hNormB v)
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hBound := hMinor L hL x Y Hprime d sep hVbig hTbLower
    blockA blockB hDisjoint m hm A B hPattern fA fB
    hfA hfB vA vB M N P Q hM hN a r beta0 theta k
    hApprox hr hcop hbeta hP hQ hR hrCap hDyadA hDyadB
  simpa only [SA,SB,fA,fB]
    using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuSignedKnuAllDenominators -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- A GENUINE original source03 signed Knu *minor* physical
bilinear estimate, not an asserted cancellation hypothesis.
The original two independent BIG marked groups, real ν
pattern, all-conductor primitive character family, real
global log-cell amplitudes, physical integer dyad windows,
original -(-1)^(cardA+cardB) and additive Fourier frequency
-k*theta are all preserved. The actual group separation, active-cell lower masses, and the
three TRUE C6 spectral scale bounds are explicit hypotheses.
Unlike the earlier signed minor theorem, no polynomial upper
cap is imposed on the Dirichlet denominator. The proof
will invoke the independently kernel-checked C281 true
ν-character-mode C6 inequality, C280 exact signed
physical expansion, C284 actual mode coefficient L1 budget
and C285 quantitative mode sum. No raw/Hoeffding
transference is claimed. -/
theorem source_original_source03_true_nu_signed_Knu_all_denominators434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (bA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (bB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (hbA : ∀ v, ‖bA v‖ ≤ 1)
    (hbB : ∀ v, ‖bB v‖ ≤ 1)
    (vA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let XA : ℕ := sourceOriginalGramPrimeProduct434 SA vA
    let XB : ℕ := sourceOriginalGramPrimeProduct434 SB vB
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then bA v else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then bB v else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ))‖^2 ≤
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2 * (125*L^(-Bsave)) := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    bA bB hbA hbB vA vB
    M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  dsimp
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let pa : SourceOriginalGramPrimeTuple434 SA → ℕ :=
    sourceOriginalGramPrimeProduct434 SA
  let pb : SourceOriginalGramPrimeTuple434 SB → ℕ :=
    sourceOriginalGramPrimeProduct434 SB
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  let XA : ℕ := pa vA
  let XB : ℕ := pb vB
  let phase : ℕ → ℕ → ℂ :=
    fun n mm => Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (((n*mm:ℕ):ℤ))
  let chars := sourceOriginalActualPrimitiveCharacters434 Qchar
  let IA := JA.product chars
  let IB := JB.product chars
  let outA : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i => sourceOriginalPrimitiveOutputCellCoefficient434
      Qchar hA massA i.1 i.2 XA
  let outB : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun j => sourceOriginalPrimitiveOutputCellCoefficient434
      Qchar hB massB j.1 j.2 XB
  let modeA : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun i v => sourceOriginalPrimitiveInputCellMode434
      Qchar hA i.1 i.2 (pa v)
  let modeB : (ℤ × (Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))) →
      SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun j v => sourceOriginalPrimitiveInputCellMode434
      Qchar hB j.1 j.2 (pb v)
  let bAW : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => if pa v ∈ AW then bA v else 0
  let bBW : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => if pb v ∈ BW then bB v else 0
  let H : SourceOriginalGramPrimeTuple434 SA ×
          SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => phase (pa v.1) (pb v.2)
  let coef :
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) →
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i j => -((-1:ℂ)^(A.card+B.card)) * outA i*outB j
  let mmode :
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) →
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) → ℂ :=
    fun i j => sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => bAW v*modeA i v)
      (fun v => bBW v*modeB j v)
      H
  let cost : ℝ := (Qchar:ℝ)^4*(xi⁻¹)^4
  let saving : ℝ := 125*L^(-Bsave)
  have hSavingPos : 0 ≤ saving := by
    dsimp [saving]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _)
  have hCostPos : 0 ≤ cost := by dsimp [cost]; positivity
  have hCoeffBudget :
      (∑ i ∈ IA, ∑ j ∈ IB, ‖coef i j‖) ≤ cost := by
    have hh := source_original_signed_minor_endpoint_l1_cost434
      Qchar (A.card+B.card) JA JB hA hB
      massA massB xi hxi hMassA hMassB hTotalA hTotalB
      XA XB
    simpa only [IA,IB,chars,outA,outB,coef,cost]
      using hh
  have hModeBudget (i : ℤ × (Σ q : Fin Qchar,
       DirichletCharacter ℂ (q.val+1)))
      (hi : i ∈ IA)
      (j : ℤ × (Σ q : Fin Qchar,
       DirichletCharacter ℂ (q.val+1)))
      (hj : j ∈ IB) :
      ‖mmode i j‖^2 ≤ saving := by
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => bA v*modeA i v
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => bB v*modeB j v
    have hFub :=
      source_original_physical_masked_mode_minor_fubini434
        wA wB pa pb bA (modeA i) bB (modeB j)
        AW BW phase
    have hNormA (v : SourceOriginalGramPrimeTuple434 SA) :
        ‖modeA i v‖ ≤ 1 := by
      dsimp [modeA]
      unfold sourceOriginalPrimitiveInputCellMode434
      split_ifs
      · rw [norm_star]
        exact i.2.2.norm_le_one _
      · simp
    have hNormB (v : SourceOriginalGramPrimeTuple434 SB) :
        ‖modeB j v‖ ≤ 1 := by
      dsimp [modeB]
      unfold sourceOriginalPrimitiveInputCellMode434
      split_ifs
      · rw [norm_star]
        exact j.2.2.norm_le_one _
      · simp
    have hfA (v : SourceOriginalGramPrimeTuple434 SA) :
        ‖fA v‖ ≤ 1 := by
      change ‖bA v * modeA i v‖ ≤ 1
      rw [norm_mul]
      calc
        _ ≤ (1:ℝ)*1 :=
          mul_le_mul (hbA v) (hNormA v) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hfB (v : SourceOriginalGramPrimeTuple434 SB) :
        ‖fB v‖ ≤ 1 := by
      change ‖bB v * modeB j v‖ ≤ 1
      rw [norm_mul]
      calc
        _ ≤ (1:ℝ)*1 :=
          mul_le_mul (hbB v) (hNormB v) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hC6 :=
      source_original_source03_true_nu_big_bounded_minor_multiplier434
        cfg x L Y Hprime d sep hVbig
        blockA blockB hDisjoint m hm A B hPattern
        fA fB hfA hfB M N P Q hM hN
        a r beta0 hr hcop hbeta hP hQ
        D Bsave hL hR hNlarge hMlarge hMNlarge
        C hExponent hSaving
    have hPhase :=
      source_original_physical_minor_fourier_phase_identity434
        SA muA SB muB fA fB AW BW theta k a r beta0 hApprox
    dsimp only at hC6
    rw [hPhase] at hC6
    change ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => (if pa v ∈ AW then bA v else 0)*modeA i v)
      (fun v => (if pb v ∈ BW then bB v else 0)*modeB j v)
      (fun v => phase (pa v.1) (pb v.2))‖^2 ≤ saving
    rw [hFub]
    simpa only [fA,fB,SA,SB,muA,muB,
      modeA,modeB,pa,pb,AW,BW,phase,saving]
      using hC6
  have hOverall :=
    source_original_finite_two_global_minor_mode_square434
      IA IB coef mmode saving cost
      hSavingPos hCostPos hModeBudget hCoeffBudget
  have hFactor :=
    source_original_physical_signed_minor_Knu_mode_expansion434
      SA muA SB muB bA bB AW BW
      Qchar JA JB hA hB massA massB XA XB
      (A.card+B.card) phase
  dsimp only at hFactor
  change
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB bAW bBW
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (pa v.1) XA (pb v.2) XB (A.card+B.card) *
        phase (pa v.1) (pb v.2))‖^2 ≤
      cost^2*saving
  rw [hFactor]
  exact hOverall
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDirichletAllRange -/

section

open Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Dirichlet approximation at the ACTUAL Fourier frequency
-k*theta, with its full (possibly superpolynomial) cutoff R.
The rational center is coprime and the error satisfies both
the sharp Dirichlet bound and the C6 hypothesis |beta|<=r^-2.
No polynomial bound on r is assumed. -/
theorem source_original_source03_dirichlet_full_frequency434
    (theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R) :
    ∃ (a : ℤ) (r : ℕ) (beta : ℝ),
      0 < r ∧ r ≤ R ∧ Int.gcd a (r:ℤ) = 1 ∧
      -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta ∧
      |beta| ≤ 1/(((R+1:ℕ):ℝ)*(r:ℝ)) ∧
      |beta| ≤ 1/(r:ℝ)^2 := by
  let alpha : ℝ := -(k:ℝ)*theta
  obtain ⟨q,hApprox,hDen⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le alpha hR
  let a : ℤ := q.num
  let r : ℕ := q.den
  have hr : 0 < r := q.pos
  have hcop : Int.gcd a (r:ℤ) = 1 := by
    change Nat.gcd q.num.natAbs q.den = 1
    exact q.reduced
  have hSharp :
      |alpha - (a:ℝ)/(r:ℝ)| ≤
        1/(((R+1:ℕ):ℝ)*(r:ℝ)) := by
    simpa only [a,r,Rat.cast_def,Nat.cast_add,Nat.cast_one] using hApprox
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hRp : 0 < ((R+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos R
  have hDenR : (r:ℝ) ≤ ((R+1:ℕ):ℝ) := by
    exact_mod_cast Nat.le_succ_of_le hDen
  have hBound : 1/(((R+1:ℕ):ℝ)*(r:ℝ)) ≤ 1/(r:ℝ)^2 := by
    apply (div_le_div_iff₀ (mul_pos hRp hrr) (pow_pos hrr 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hDenR hrr.le]
  refine ⟨a,r,alpha-(a:ℝ)/(r:ℝ),hr,hDen,hcop,?_,?_,?_⟩
  · dsimp [alpha]
    ring
  · exact hSharp
  · exact hSharp.trans hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCoarseRectangleDirichlet -/

section

open Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ONE coprime Dirichlet approximation for the WHOLE coarse rectangle.
The cutoff floor(M*N/S) controls the slow phase by |beta| *M*N<=S/r.
In the complementary denominator range it supplies all four genuine
C6 scale inequalities. No fine-cell index or character/retention
exponent occurs; the actual frequency remains exactly -k*theta. -/
theorem source_original_coarse_rectangle_dirichlet_dichotomy434
    (theta : ℝ) (k : ℤ)
    (M N Qchar : ℕ) (hM : 0 < M) (hN : 0 < N)
    (S T : ℝ) (hS : 1 ≤ S) (hT : 0 ≤ T)
    (hSscale : S ≤ (M:ℝ)*(N:ℝ))
    (hQ : T ≤ (Qchar:ℝ))
    (hNscale : T ≤ (N:ℝ))
    (hMscale : T*Real.log (2*((M:ℝ)*(N:ℝ))) ≤ (M:ℝ))
    (hLogscale : T*Real.log (2*((M:ℝ)*(N:ℝ))) ≤ S) :
    ∃ (a : ℤ) (r : ℕ) (beta : ℝ),
      0 < r ∧ Int.gcd a (r:ℤ) = 1 ∧
      -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta ∧
      |beta| ≤ 1/(r:ℝ)^2 ∧
      |beta| *((M:ℝ)*(N:ℝ)) ≤ S/(r:ℝ) ∧
      (r:ℝ) ≤ ((M:ℝ)*(N:ℝ))/S ∧
      (r ≤ Qchar ∨
        (Qchar < r ∧
         T ≤ (r:ℝ) ∧ T ≤ (N:ℝ) ∧
         T*Real.log (2*(r:ℝ)) ≤ (M:ℝ) ∧
         T*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))) := by
  have hSp : 0 < S := by linarith
  have hMNp : 0 < (M:ℝ)*(N:ℝ) := by positivity
  have hRatio : 1 ≤ ((M:ℝ)*(N:ℝ))/S :=
    (le_div_iff₀ hSp).2 (by simpa using hSscale)
  let R : ℕ := ⌊((M:ℝ)*(N:ℝ))/S⌋₊
  have hR : 0 < R := Nat.floor_pos.mpr hRatio
  obtain ⟨a,r,beta,hr,hrR,hcop,hApprox,hSharp,hBeta⟩ :=
    source_original_source03_dirichlet_full_frequency434 theta k R hR
  have hrp : 0 < (r:ℝ) := by exact_mod_cast hr
  have hRp : 0 < ((R+1:ℕ):ℝ) := by positivity
  have hFloor : (R:ℝ) ≤ ((M:ℝ)*(N:ℝ))/S :=
    Nat.floor_le (by positivity)
  have hrRreal : (r:ℝ) ≤ (R:ℝ) := by exact_mod_cast hrR
  have hCap : (r:ℝ) ≤ ((M:ℝ)*(N:ℝ))/S := hrRreal.trans hFloor
  have hFloorUpper : ((M:ℝ)*(N:ℝ))/S < ((R+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      Nat.lt_floor_add_one (((M:ℝ)*(N:ℝ))/S)
  have hMNUpper : (M:ℝ)*(N:ℝ) ≤ ((R+1:ℕ):ℝ)*S :=
    le_of_lt ((div_lt_iff₀ hSp).mp hFloorUpper)
  have hSlow : |beta| *((M:ℝ)*(N:ℝ)) ≤ S/(r:ℝ) := by
    calc
      _ ≤ (1/(((R+1:ℕ):ℝ)*(r:ℝ)))*((M:ℝ)*(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hSharp hMNp.le
      _ ≤ (1/(((R+1:ℕ):ℝ)*(r:ℝ)))*(((R+1:ℕ):ℝ)*S) :=
        mul_le_mul_of_nonneg_left hMNUpper (by positivity)
      _ = S/(r:ℝ) := by field_simp
  refine ⟨a,r,beta,hr,hcop,hApprox,hBeta,hSlow,hCap,?_⟩
  by_cases hMajor : r ≤ Qchar
  · exact Or.inl hMajor
  · right
    have hMinor : Qchar < r := Nat.lt_of_not_ge hMajor
    have hTr : T ≤ (r:ℝ) := hQ.trans (by exact_mod_cast hMinor.le)
    have hRprod : (r:ℝ)*S ≤ (M:ℝ)*(N:ℝ) :=
      (le_div_iff₀ hSp).mp hCap
    have hRle : (r:ℝ) ≤ (M:ℝ)*(N:ℝ) := by nlinarith
    have hLog : Real.log (2*(r:ℝ)) ≤
        Real.log (2*((M:ℝ)*(N:ℝ))) :=
      Real.log_le_log (by positivity) (by linarith)
    have hMLocal : T*Real.log (2*(r:ℝ)) ≤ (M:ℝ) :=
      (mul_le_mul_of_nonneg_left hLog hT).trans hMscale
    have hProduct : T*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ) := by
      calc
        _ = (r:ℝ)*(T*Real.log (2*(r:ℝ))) := by ring
        _ ≤ (r:ℝ)*(T*Real.log (2*((M:ℝ)*(N:ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hLog hT) hrp.le
        _ ≤ (r:ℝ)*S := mul_le_mul_of_nonneg_left hLogscale hrp.le
        _ ≤ (M:ℝ)*(N:ℝ) := hRprod
    exact ⟨hMinor,hTr,hNscale,hMLocal,hProduct⟩

/-- A nonempty EXPONENT budget for the new minor/coarse/major geometry.
This certifies numerical feasibility, not the still-required uniform
instantiation of all physical data and the global signed transference.
Cq and Cxi can be chosen after D without changing the minor saving. -/
theorem source_original_aligned_comparison_exponent_witness434
    (Bgoal d Cfactor Cfreq : ℝ)
    (hGoal : 0 ≤ Bgoal) (hd : 0 ≤ d)
    (hFactor : 0 ≤ Cfactor) (hFreq : 0 ≤ Cfreq) :
    ∃ (Bsave D Cq Cs C4 H Cxi Bmajor : ℝ),
      0 < Bsave ∧ 0 ≤ D ∧
      Bgoal+(2*d+4)+2 ≤ Bsave ∧
      Bsave+2*Cfactor ≤ D ∧
      D+1 ≤ Cq ∧
      D+d+2 ≤ Cs ∧
      Cs+1 ≤ C4 ∧ Cfreq ≤ C4 ∧
      Bsave ≤ 2*Bmajor ∧
      Bmajor+4*Cq+C4+2 ≤ H ∧
      Bsave+H+d+4 ≤ Cxi := by
  let Bsave := Bgoal+2*d+6
  let D := Bsave+2*Cfactor
  let Cq := D+1
  let Cs := D+d+2
  let C4 := Cs+1+Cfreq
  let Bmajor := Bsave
  let H := Bmajor+4*Cq+C4+2
  let Cxi := Bsave+H+d+4
  refine ⟨Bsave,D,Cq,Cs,C4,H,Cxi,Bmajor,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [Bsave,D,Cq,Cs,C4,H,Cxi,Bmajor]
  all_goals linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCoarseDirichlet -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The coarse-rectangle Dirichlet dichotomy is UNIFORMLY applicable to
actual original prime products, with at most C0*log L groups and tmax
probes per group. The threshold precedes ALL moving finite data.
Original BIG-prime lower and upper support assumptions are explicit.
No fixed bound on the total number of freed labels is used. -/
theorem eventually_source_original_ACTUAL_coarse_dirichlet434
    (cfg : SourceComparisonFixed434) (dscale D : ℝ)
    (hd : 0 ≤ dscale) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (blockA blockB : Finset β)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (vA : SourceOriginalGramPrimeTuple434 (fun z : ν.1 => d.Tb z.val.1))
      (vB : SourceOriginalGramPrimeTuple434 (fun z : ν.2 => d.Tb z.val.1))
      (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
      (hWindowA : (M:ℝ) ≤ (sourceOriginalGramPrimeProduct434
        (fun z : ν.1 => d.Tb z.val.1) vA:ℝ) ∧
        (sourceOriginalGramPrimeProduct434 (fun z : ν.1 => d.Tb z.val.1) vA:ℝ) ≤ 2*(M:ℝ))
      (hWindowB : (N:ℝ) ≤ (sourceOriginalGramPrimeProduct434
        (fun z : ν.2 => d.Tb z.val.1) vB:ℝ) ∧
        (sourceOriginalGramPrimeProduct434 (fun z : ν.2 => d.Tb z.val.1) vB:ℝ) ≤ 2*(N:ℝ))
      (theta : ℝ) (k : ℤ) (Qchar : ℕ) (hQ : L^D ≤ (Qchar:ℝ)),
    ∃ (a : ℤ) (r : ℕ) (beta : ℝ),
      0 < r ∧ Int.gcd a (r:ℤ) = 1 ∧
      -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta ∧
      |beta| ≤ 1/(r:ℝ)^2 ∧
      |beta| *((M:ℝ)*(N:ℝ)) ≤ L^(D+dscale+2)/(r:ℝ) ∧
      (r:ℝ) ≤ ((M:ℝ)*(N:ℝ))/L^(D+dscale+2) ∧
      (r ≤ Qchar ∨
        (Qchar < r ∧
         L^D ≤ (r:ℝ) ∧ L^D ≤ (N:ℝ) ∧
         L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ) ∧
         L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))) := by
  have hc : 0 < cfg.cexp := by linarith [cfg.haexp,cfg.hab,cfg.hbc]
  have hPower : 0 ≤ D+dscale+2 := by linarith
  obtain ⟨L0,hExp⟩ := source_original_circle_eventual_exp_dominance434
    cfg.cexp (D+dscale+2) 0 hc hPower (by norm_num)
  let cslot : ℝ := (cfg.tmax:ℝ)*cfg.C0
  let c : ℝ := 2*cslot+Real.log 2
  have hcs : 0 ≤ cslot := mul_nonneg (Nat.cast_nonneg _) cfg.hC0
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  filter_upwards [eventually_ge_atTop L0,eventually_ge_atTop (max (4:ℝ) c)]
    with L hL0 hLc
  have hL : 1 ≤ L := by have hh := (le_max_left (4:ℝ) c).trans hLc; linarith
  have hLp : 0 < L := by linarith
  have hcL : c ≤ L := (le_max_right _ _).trans hLc
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLp]
  have hPow1 : 1 ≤ L^dscale := Real.one_le_rpow hL hd
  have hPow0 : 0 ≤ L^dscale := Real.rpow_nonneg hLp.le _
  have hS1 : 1 ≤ L^(D+dscale+2) := Real.one_le_rpow hL hPower
  have hExpBound : 4*L^(D+dscale+2) ≤ Real.exp (L^cfg.cexp) := by
    have hh := (hExp L hL0).2 1 (by norm_num) (by simp)
    simpa using hh
  intro ι β instI instDI instB instDB x Y Hprime d blockA blockB
    m hm ν hPattern hTbLower hTbUpper vA vB M N hM hN hWindowA hWindowB theta k Qchar hQ
  classical
  have hSlots (A : Finset (β × Fin m)) :
      (Fintype.card A:ℝ) ≤ cslot*Real.log L := by
    calc
      (Fintype.card A:ℝ) = (A.card:ℝ) := by simp
      _ ≤ (Fintype.card (β × Fin m):ℝ) := by exact_mod_cast Finset.card_le_univ A
      _ = (Fintype.card β:ℝ)*(m:ℝ) := by simp
      _ ≤ (cfg.C0*Real.log L)*(cfg.tmax:ℝ) :=
        mul_le_mul d.hBigGroups (by exact_mod_cast hm)
          (Nat.cast_nonneg _) (mul_nonneg cfg.hC0 hLogL)
      _ = cslot*Real.log L := by dsimp [cslot]; ring
  have hUpper (A : Finset (β × Fin m))
      (v : SourceOriginalGramPrimeTuple434 (fun z : A => d.Tb z.val.1)) :
      Real.log ((sourceOriginalGramPrimeProduct434 (fun z : A => d.Tb z.val.1) v):ℝ) ≤
        cslot*Real.log L*L^dscale := by
    have hPos (z : A) : (0:ℝ) < (v z).val := by
      exact_mod_cast (d.hTbPrime z.val.1 (v z).val (v z).property).pos
    have hLog (z : A) : Real.log ((v z).val:ℝ) ≤ L^dscale := by
      have hh := Real.log_le_log (hPos z) (hTbUpper z.val.1 (v z).val (v z).property)
      simpa only [Real.log_exp] using hh
    calc
      _ = ∑ z : A, Real.log ((v z).val:ℝ) := by
        unfold sourceOriginalGramPrimeProduct434
        rw [Nat.cast_prod,Real.log_prod]
        intro z hz
        exact (hPos z).ne'
      _ ≤ ∑ _z : A, L^dscale := Finset.sum_le_sum (fun z hz => hLog z)
      _ = (Fintype.card A:ℝ)*L^dscale := by simp
      _ ≤ cslot*Real.log L*L^dscale :=
        mul_le_mul_of_nonneg_right (hSlots A) hPow0
  have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hLogM := (Real.log_le_log hMp hWindowA.1).trans (hUpper ν.1 vA)
  have hLogN := (Real.log_le_log hNp hWindowB.1).trans (hUpper ν.2 vB)
  have hLogMN : Real.log (2*((M:ℝ)*(N:ℝ))) ≤ L^(dscale+2) := by
    have hLPow : 1 ≤ L*L^dscale := by nlinarith
    have hSlotBound : 2*cslot*Real.log L*L^dscale ≤ 2*cslot*L*L^dscale :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogL (by positivity)) hPow0
    calc
      _ = Real.log 2 + Real.log (M:ℝ) + Real.log (N:ℝ) := by
        rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (mul_pos hMp hNp).ne',
          Real.log_mul hMp.ne' hNp.ne']
        ring
      _ ≤ Real.log 2 + 2*cslot*Real.log L*L^dscale := by linarith
      _ ≤ c*L*L^dscale := by
        have hh := mul_le_mul_of_nonneg_left hLPow hlog2
        dsimp [c]
        nlinarith
      _ ≤ L*L*L^dscale := by gcongr
      _ = L^(dscale+2) := by rw [Real.rpow_add hLp,Real.rpow_two]; ring
  obtain ⟨hLowerA,hLowerB⟩ :=
    source_original_source03_true_nu_big_long_products434
      cfg x L Y Hprime d hLp.le blockA blockB m ν.1 ν.2 hPattern
      hTbLower vA vB
  have hLargeM : L^(D+dscale+2) ≤ (M:ℝ) := by
    have hh := hExpBound.trans (hLowerA.trans hWindowA.2)
    linarith
  have hLargeN : L^(D+dscale+2) ≤ (N:ℝ) := by
    have hh := hExpBound.trans (hLowerB.trans hWindowB.2)
    linarith
  have hPowMul : L^D*L^(dscale+2) = L^(D+dscale+2) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hLogscale : L^D*Real.log (2*((M:ℝ)*(N:ℝ))) ≤ L^(D+dscale+2) := by
    calc
      _ ≤ L^D*L^(dscale+2) :=
        mul_le_mul_of_nonneg_left hLogMN (Real.rpow_nonneg hLp.le _)
      _ = _ := hPowMul
  have hSscale : L^(D+dscale+2) ≤ (M:ℝ)*(N:ℝ) := by
    have hN1 : 1 ≤ (N:ℝ) := hS1.trans hLargeN
    exact hLargeM.trans (by nlinarith)
  have hNscale : L^D ≤ (N:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith : D ≤ D+dscale+2)).trans hLargeN
  exact source_original_coarse_rectangle_dirichlet_dichotomy434
    theta k M N Qchar hM hN
    (L^(D+dscale+2)) (L^D) hS1 (Real.rpow_nonneg hLp.le _)
    hSscale hQ hNscale (hLogscale.trans hLargeM) hLogscale
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuSelectedAtomProbability -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Original source03 ν-selected independent A/B labelled-prime
tuple laws push forward to EXACT positive normalized integer
product atom measures. Every group normalization is the true
1/(p*V_g), with V_g the actual prime reciprocal sum. This is
uniform in the selected first/second probe blocks and keeps
repeated numeric primes within each genuine group law. -/
theorem source_original_true_nu_selected_atom_probability434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hVbig : ∀ g : β, d.Vbig g =
      ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (m : ℕ) (A B : Finset (β × Fin m)) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    (∀ n ∈ TA, 0 < sourceOriginalPhysicalProductAtom434 SA muA n) ∧
    (∀ n ∈ TB, 0 < sourceOriginalPhysicalProductAtom434 SB muB n) ∧
    (∑ n ∈ TA, sourceOriginalPhysicalProductAtom434 SA muA n) = 1 ∧
    (∑ n ∈ TB, sourceOriginalPhysicalProductAtom434 SB muB n) = 1 := by
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  have hPosA (n : ℕ) (hn : n ∈ TA) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n := by
    exact source_original_true_prime_harmonic_atom_pos434
      SA (fun z => d.Vbig z.val.1)
      (fun z => cfg.hv.trans_le (d.hVbig z.val.1))
      (fun z p hp => d.hTbPrime z.val.1 p hp) n hn
  have hPosB (n : ℕ) (hn : n ∈ TB) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n := by
    exact source_original_true_prime_harmonic_atom_pos434
      SB (fun z => d.Vbig z.val.1)
      (fun z => cfg.hv.trans_le (d.hVbig z.val.1))
      (fun z p hp => d.hTbPrime z.val.1 p hp) n hn
  have hNormA (z : A) : ∑ p ∈ SA z, muA z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hNormB (z : B) : ∑ p ∈ SB z, muB z p = 1 := by
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hv := source_prime_shared_atom_total434
      (d.Tb z.val.1) (d.Vbig z.val.1)
      (hVbig z.val.1) hVpos.ne'
    change (∑ p ∈ d.Tb z.val.1,
      ((1/(p:ℝ))/(d.Vbig z.val.1))) = 1
    calc
      _ = ∑ p ∈ d.Tb z.val.1,
        sourcePrimeSharedAtom434 (d.Vbig z.val.1) p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [sourcePrimeSharedAtom434]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ac_rfl
      _ = 1 := hv
  have hTotalA :=
    source_original_physical_atom_support_total434 SA muA hNormA
  have hTotalB :=
    source_original_physical_atom_support_total434 SB muB hNormB
  exact ⟨hPosA,hPosB,hTotalA,hTotalB⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuKnuSelectedCellMellinOperator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The genuine SOURCE03 primitive Knu Fourier/Mellin MINOR operator on
arbitrary selected output TWO-INTEGER coefficient vectors
restricted to the ACTUAL original GLOBAL jA/jB log cells,
with the TRUE original reciprocal-prime harmonic atom mass.
The auxiliary D_A,D_B variables are restricted to ONE real
dyadic input-window pair; all ATTAINABLE outputs nA,nB vary
independently. The output-UNIFORM actual C6 saving is transferred
to arbitrary weighted L2 coefficient tests by the sharp finite
inverse-atom Cauchy-Schwarz theorem and exact positive SUBprobability laws on the original cell atoms.
No assumption that H(nA,nB) factors, and no loss equal to
the number of selected outputs. Full auxiliary dyad/global
ν summation and signed RAW cancellation remain separate. -/
theorem source_original_true_nu_Knu_selected_CELL_output_mellin_operator_minor434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    ∀ L : ℝ, 1 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (jA jB : ℤ) (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hA n=jA)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hB n=jB)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let H : ℕ → ℕ → ℂ := fun XA XB =>
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB
        (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
          then (1:ℂ) else 0)
        (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
          then (1:ℂ) else 0)
        (fun v =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB hA hB massA massB
            (sourceOriginalGramPrimeProduct434 SA v.1) XA
            (sourceOriginalGramPrimeProduct434 SB v.2) XB
            (A.card+B.card) *
          Green64SourceC6.integerPhase (-(k:ℝ)*theta)
            (((sourceOriginalGramPrimeProduct434 SA v.1 *
               sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let budget : ℝ :=
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
    ‖(∑ n ∈ TA, ∑ mm ∈ TB, aCoeff n*bCoeff mm*H n mm)‖^2 ≤
      budget*EA*EB := by
  intro L hL ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    jA jB ζ aCoeff bCoeff M N P Q hM hN
    a r beta0 theta k hApprox
    hr hcop hbeta hP hQ hR hNlarge hMlarge hMNlarge
  classical
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 hA n=jA)
  let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 hB n=jB)
  let AW := (Finset.range P).image (fun i => M+i)
  let BW := (Finset.range Q).image (fun j => N+j)
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let H : ℕ → ℕ → ℂ := fun XA XB =>
    sourceOriginalFiniteTwoSidedMinorBilinear434
      wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
        then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
        then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB hA hB massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (A.card+B.card) *
        Green64SourceC6.integerPhase (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let budget : ℝ :=
    (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
  let eps : ℝ := Real.sqrt budget
  have hBudget : 0 ≤ budget := by
    dsimp [budget]
    positivity
  have hEps : 0 ≤ eps := Real.sqrt_nonneg _
  have hEpsSq : eps^2 = budget := Real.sq_sqrt hBudget
  obtain ⟨hPosAFull,hPosBFull,hTotAFull,hTotBFull⟩ :=
    source_original_true_nu_selected_atom_probability434
      cfg x L Y Hprime d hVbig m A B
  have hPosA (n : ℕ) (hn : n∈TA) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n :=
    hPosAFull n (Finset.mem_filter.mp hn).1
  have hPosB (n : ℕ) (hn : n∈TB) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n :=
    hPosBFull n (Finset.mem_filter.mp hn).1
  have hTotA :
      (∑ n∈TA, sourceOriginalPhysicalProductAtom434 SA muA n) ≤ 1 := by
    calc
      _ ≤ ∑ n∈sourceOriginalPhysicalProductAtomSupport434 SA,
          sourceOriginalPhysicalProductAtom434 SA muA n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun n hn hnot => (hPosAFull n hn).le)
      _ = 1 := hTotAFull
  have hTotB :
      (∑ n∈TB, sourceOriginalPhysicalProductAtom434 SB muB n) ≤ 1 := by
    calc
      _ ≤ ∑ n∈sourceOriginalPhysicalProductAtomSupport434 SB,
          sourceOriginalPhysicalProductAtom434 SB muB n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun n hn hnot => (hPosBFull n hn).le)
      _ = 1 := hTotBFull
  have hKernel (nA : ℕ) (hnA : nA ∈ TA)
      (nB : ℕ) (hnB : nB ∈ TB) :
      ‖H nA nB‖ ≤ eps := by
    have hPoint := source_original_true_nu_Knu_actual_output_atom_mellin_minor434
      cfg D Bsave hD C hExponent hSaving
      L hL x Y Hprime d sep hVbig
      blockA blockB hDisjoint m hm A B hPattern
      Qchar JA JB hA hB massA massB xi hxi
      hMassA hMassB hTotalA hTotalB
      ζ nA nB (Finset.mem_filter.mp hnA).1
        (Finset.mem_filter.mp hnB).1 M N P Q hM hN
      a r beta0 theta k hApprox hr hcop hbeta
      hP hQ hR hNlarge hMlarge hMNlarge
    have hh : ‖H nA nB‖^2 ≤ budget := by
      change ‖H nA nB‖^2 ≤ budget at hPoint
      exact hPoint
    nlinarith [norm_nonneg (H nA nB)]
  have hOp := source_original_finite_subprobability_atom_kernel_operator434
    TA TB
    (sourceOriginalPhysicalProductAtom434 SA muA)
    (sourceOriginalPhysicalProductAtom434 SB muB)
    hPosA hPosB hTotA hTotB
    aCoeff bCoeff H eps hEps hKernel
  change ‖(∑ n ∈ TA, ∑ mm ∈ TB,
    aCoeff n*bCoeff mm*H n mm)‖^2 ≤ eps^2*EA*EB at hOp
  rw [hEpsSq] at hOp
  exact hOp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuKnuCircleSelectedCellMellin -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ORIGINAL SOURCE03 signed primitive comparison Knu on
the real physical two-BIG-block prime law has a genuinely
selected active-output GLOBAL-cell inverse-atom weighted-L2
Fourier/Mellin C6 bound outside its OWN physical moving rational
arc. Both input-window C6 denominator/scale conditions are
derived from Dirichlet circle arithmetic, not separately
postulated; no output atom-count loss or fake factorization.
This is a single matched input dyad, not yet all four rectangles.
Per-output active-cell coefficients and true prime separation
remain explicit original source03 arithmetic assumptions. -/
theorem eventually_source_original_true_nu_Knu_circle_selected_CELL_mellin_operator434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc Chigh : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (massA massB : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (jA jB : ℤ) (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (U1 U2 Hcell : ℝ)
    (hU1 : Real.exp (L^cfg.cexp-1) ≤ U1)
    (hU2 : Real.exp (L^cfg.cexp-1) ≤ U2)
    (hH : Hcell = U1*U2) (hHp : 0 < Hcell)
    (hHupper :
      Hcell ≤ Real.exp (Chigh*Real.log L*L^(1/2:ℝ)))
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hCellA : U1 ≤ (M:ℝ)) (hCellB : U2 ≤ (N:ℝ))
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/Hcell)),
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hA n=jA)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hB n=jB)
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let H : ℕ → ℕ → ℂ := fun XA XB =>
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB
        (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
          then (1:ℂ) else 0)
        (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
          then (1:ℂ) else 0)
        (fun v =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB hA hB massA massB
            (sourceOriginalGramPrimeProduct434 SA v.1) XA
            (sourceOriginalGramPrimeProduct434 SB v.2) XB
            (A.card+B.card) *
          Green64SourceC6.integerPhase (-(k:ℝ)*theta)
            (((sourceOriginalGramPrimeProduct434 SA v.1 *
               sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let budget : ℝ :=
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
    ‖(∑ n ∈ TA, ∑ mm ∈ TB, aCoeff n*bCoeff mm*H n mm)‖^2 ≤
      budget*EA*EB := by
  have hc : 0 < cfg.cexp := by
    linarith [cfg.haexp,cfg.hab,cfg.hbc]
  have hCircle :=
    eventually_source_original_circle_physical_C6_scales434
      cfg.cexp (1/2:ℝ) Aarc D cfg.Carc 1 1 Chigh
      hc (by norm_num) hAarc hD hArc hChigh
  filter_upwards [hCircle] with L hCircleL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    jA jB ζ aCoeff bCoeff
    U1 U2 Hcell hU1 hU2 hH hHp hHupper
    M N P Q hM hN hP hQ hCellA hCellB
    theta k hk hOutside
  obtain ⟨a,r,hr,hcop,hNear,hR,hNlarge,hMlarge,hMNlarge⟩ :=
    hCircleL.2 U1 U2 Hcell hU1 hU2 hH hHp
      hHupper M N hCellA hCellB theta k hk hOutside
  let beta0 : ℝ := -(k:ℝ)*theta-(a:ℝ)/(r:ℝ)
  have hApprox : -(k:ℝ)*theta =
      (a:ℝ)/(r:ℝ)+beta0 := by
    dsimp [beta0]
    ring
  have hbeta : |beta0| ≤ 1/((r:ℝ)^2) := by
    simpa only [beta0] using hNear
  exact source_original_true_nu_Knu_selected_CELL_output_mellin_operator_minor434
    cfg D Bsave hD C hExponent hSaving
    L (by linarith [hCircleL.1] : 1 ≤ L) x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm A B hPattern
    Qchar JA JB hA hB massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    jA jB ζ aCoeff bCoeff
    M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ hR hNlarge hMlarge hMNlarge
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexKnuSelectedCellMellin -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original SOURCE03 FIVE-INDEX signed primitive Knu C6 estimate
for all selected output two-integer atoms in the ACTUAL active
GLOBAL jA/jB cells, on EACH original auxiliary dyad [M,2M)x
[N,2N) naturally attached to this mode.
The full original moving Hcell and its growth bounds, genuine
BIG-group lower scales, and the large coprime Dirichlet
denominator are derived, not assumed as independent hypotheses.
Four possible M/N choices are allowed; Fourier -k theta, pure
Mellin zeta, harmonic atom weights and arbitrary output
coefficient vectors are kept exact. No global four-dyad sum yet. -/
theorem eventually_source_original_true_five_index_Knu_selected_CELL_mellin_operator434
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
    (M N : ℕ)
    (hMchoice :
      M = Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1)) ∨
      M = 2*Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1)))
    (hNchoice :
      N = Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1)) ∨
      N = 2*Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1)))
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
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1)
    let AW : Finset ℕ := (Finset.range M).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range N).image (fun j => N+j)
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let H : ℕ → ℕ → ℂ := fun XA XB =>
      sourceOriginalFiniteTwoSidedMinorBilinear434
        wA wB
        (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈ AW
          then (1:ℂ) else 0)
        (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈ BW
          then (1:ℂ) else 0)
        (fun v =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB (hAvar z.1) (hBvar z.1) massA massB
            (sourceOriginalGramPrimeProduct434 SA v.1) XA
            (sourceOriginalGramPrimeProduct434 SB v.2) XB
            (z.1.1.card+z.1.2.card) *
          Green64SourceC6.integerPhase (-(k:ℝ)*theta)
            (((sourceOriginalGramPrimeProduct434 SA v.1 *
               sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let budget : ℝ :=
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
    ‖(∑ n ∈ TA, ∑ mm ∈ TB, aCoeff n*bCoeff mm*H n mm)‖^2 ≤
      budget*EA*EB := by
  let Chigh : ℝ := 2*(cfg.tmax:ℝ)*cfg.C0
  have hChigh : 0 ≤ Chigh := by
    dsimp [Chigh]
    exact mul_nonneg (by positivity) cfg.hC0
  have hCircle :=
    eventually_source_original_true_nu_Knu_circle_selected_CELL_mellin_operator434
      cfg D Bsave hD C hExponent hSaving
      Aarc Chigh hAarc hArc hChigh
  filter_upwards [hCircle,eventually_ge_atTop (4:ℝ)]
    with L hCircleL hL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint
    m Qchar hm hTbLower hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff M N hMchoice hNchoice theta k hk hOutside
  let UA : ℝ := Real.exp ((z.2.1.1:ℝ)*hAvar z.1)
  let UB : ℝ := Real.exp ((z.2.2.1:ℝ)*hBvar z.1)
  let HC : ℝ := sourceOriginalProbeTrueHprime434
    m Qchar hAvar hBvar z
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m :=
    (Finset.mem_sigma.mp hz).1
  obtain ⟨hU1,hU2,hH,hHupper⟩ :=
    source_original_source03_true_five_index_circle_scales434
      cfg x L Y Hprime d (by linarith : 1 ≤ L)
      blockA blockB m Qchar hm hTbLower
      hAvar hBvar hhA hhB xi z hz
  have hM0 : 0 < Nat.ceil UA := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hN0 : 0 < Nat.ceil UB := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hMp : 0 < M := by
    rcases hMchoice with hm | hm
    · rw [hm];exact hM0
    · rw [hm]
      change 0 < 2 * Nat.ceil UA
      omega
  have hNp : 0 < N := by
    rcases hNchoice with hn | hn
    · rw [hn];exact hN0
    · rw [hn]
      change 0 < 2 * Nat.ceil UB
      omega
  have hMA : UA ≤ (M:ℝ) := by
    have hh : UA ≤ (Nat.ceil UA:ℝ) := Nat.le_ceil UA
    rcases hMchoice with hm | hm
    · rw [hm];exact hh
    · rw [hm]
      have hNN : (0:ℝ) ≤ (Nat.ceil UA:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hNB : UB ≤ (N:ℝ) := by
    have hh : UB ≤ (Nat.ceil UB:ℝ) := Nat.le_ceil UB
    rcases hNchoice with hn | hn
    · rw [hn];exact hh
    · rw [hn]
      have hNN : (0:ℝ) ≤ (Nat.ceil UB:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hHp : 0 < HC := by
    change 0 < UA*UB
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hBound := hCircleL x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm z.1.1 z.1.2 hν
    Qchar JA JB (hAvar z.1) (hBvar z.1) massA massB xi hxi
    hMassA hMassB hTotalA hTotalB
    z.2.1.1 z.2.2.1 ζ aCoeff bCoeff
    UA UB HC hU1 hU2 hH hHp hHupper
    M N M N hMp hNp (le_refl _) (le_refl _)
    hMA hNB theta k hk hOutside
  simpa only [UA,UB,HC,Chigh] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexFourMatchedC6Mellin -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- True original FIVE-index moving OWN minor-arc C6 saving for
ALL FOUR actual matched dyadic windows, including
D_A in [M0,2M0) or [2M0,4M0), independently D_B
in [N0,2N0) or [2N0,4N0), for every genuine selected
output integer atom jA/jB and arbitrary complex L2 tests.
Each of the four bounds follows from the ACTUAL arithmetic C6
with real prime intervals and Dirichlet large denominator.
Neither an output cardinality nor an all-window logarithmic
loss is hidden. Summing four physical masks still requires the
exact rectangle Fubini identification. -/
theorem eventually_source_original_true_five_index_Knu_FOUR_matched_CELL_mellin_operator434
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
            m Qchar hAvar hBvar z)),
    let SA : z.1.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : z.1.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1)
    let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
    let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let Hwin : ℕ → ℕ → ℕ → ℕ → ℂ := fun M N XA XB =>
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
        (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈
          (Finset.range M).image (fun i => M+i) then (1:ℂ) else 0)
        (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈
          (Finset.range N).image (fun j => N+j) then (1:ℂ) else 0)
        (fun v =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB (hAvar z.1) (hBvar z.1)
            massA massB
            (sourceOriginalGramPrimeProduct434 SA v.1) XA
            (sourceOriginalGramPrimeProduct434 SB v.2) XB
            (z.1.1.card+z.1.2.card) *
          Green64SourceC6.integerPhase (-(k:ℝ)*theta)
            (((sourceOriginalGramPrimeProduct434 SA v.1 *
               sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let budget : ℝ :=
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
    ‖(∑ n ∈ TA, ∑ mm ∈ TB,
      aCoeff n*bCoeff mm*Hwin M0 N0 n mm)‖^2 ≤ budget*EA*EB ∧
    ‖(∑ n ∈ TA, ∑ mm ∈ TB,
      aCoeff n*bCoeff mm*Hwin M0 (2*N0) n mm)‖^2 ≤ budget*EA*EB ∧
    ‖(∑ n ∈ TA, ∑ mm ∈ TB,
      aCoeff n*bCoeff mm*Hwin (2*M0) N0 n mm)‖^2 ≤ budget*EA*EB ∧
    ‖(∑ n ∈ TA, ∑ mm ∈ TB,
      aCoeff n*bCoeff mm*Hwin (2*M0) (2*N0) n mm)‖^2 ≤ budget*EA*EB := by
  have hGeometry :=
    eventually_source_original_true_five_index_Knu_selected_CELL_mellin_operator434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hGeometry] with L hGeometryL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1)
  let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1)
  let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
  let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let Hwin : ℕ → ℕ → ℕ → ℕ → ℂ := fun M N XA XB =>
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈
        (Finset.range M).image (fun i => M+i) then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈
        (Finset.range N).image (fun j => N+j) then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB (hAvar z.1) (hBvar z.1)
          massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (z.1.1.card+z.1.2.card) *
        Green64SourceC6.integerPhase (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
        sourceOriginalPureMellinPhase434 ζ
          (sourceOriginalGramPrimeProduct434 SA v.1 *
           sourceOriginalGramPrimeProduct434 SB v.2))
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let budget : ℝ :=
    (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
  have hWindow (M N : ℕ)
      (hMchoice : M=M0 ∨ M=2*M0)
      (hNchoice : N=N0 ∨ N=2*N0) :
      ‖(∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*Hwin M N n mm)‖^2 ≤
          budget*EA*EB := by
    have hh := hGeometryL x Y Hprime d sep hVbig
      blockA blockB hDisjoint m Qchar hm hTbLower
      hAvar hBvar hhA hhB xi hxi z hz
      JA JB massA massB hMassA hMassB hTotalA hTotalB
      ζ aCoeff bCoeff M N hMchoice hNchoice theta k hk hOutside
    change ‖(∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*Hwin M N n mm)‖^2 ≤
          budget*EA*EB at hh
    exact hh
  exact ⟨hWindow M0 N0 (Or.inl rfl) (Or.inl rfl),
    hWindow M0 (2*N0) (Or.inl rfl) (Or.inr rfl),
    hWindow (2*M0) N0 (Or.inr rfl) (Or.inl rfl),
    hWindow (2*M0) (2*N0) (Or.inr rfl) (Or.inr rfl)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueOwnActiveFamilyBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Every GENUINE original ν/active GLOBAL/primitive-character
five-index mode carries its OWN pattern and both correct
active SOURCE-B/TARGET-A GLOBAL cell witnesses.
This removes independent hActiveA/hActiveB hypotheses
when applying the verified per-mode C192 own-major theorem. -/
theorem source_original_true_own_expanded_family_active434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi : ℝ) (z : SourceOriginalTrueFiveIndex434 G m Q)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi) :
    z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m ∧
    z.2.1.1 ∈ sourceOriginalProbeActiveCellsA434
      m P V z.1 (hA z.1) xi ∧
    z.2.2.1 ∈ sourceOriginalProbeActiveCellsB434
      m P V z.1 (hB z.1) xi := by
  classical
  have hmem := Finset.mem_sigma.mp hz
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := hmem.1
  have hPair := Finset.mem_product.mp hmem.2
  have hAcell : z.2.1.1 ∈
      sourceOriginalProbeActiveCellsA434
        m P V z.1 (hA z.1) xi :=
    (Finset.mem_product.mp hPair.1).1
  have hBcell : z.2.2.1 ∈
      sourceOriginalProbeActiveCellsB434
        m P V z.1 (hB z.1) xi :=
    (Finset.mem_product.mp hPair.2).1
  exact ⟨hν,hAcell,hBcell⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueActualModeFromActiveCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- A genuine original SOURCE03 ν with nonempty active
target-A and source-B GLOBAL cell families and a positive
primitive conductor cutoff Q has a TRUE five-index witness.
The witness uses the ACTUAL level-1 primitive Dirichlet
character from the original all-conductor family.
No synthetic hExistsMode axiom is introduced. -/
theorem source_original_true_active_cells_have_actual_mode434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ) (hQ : 0 < Q)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi : ℝ) (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m)
    (hActiveA : (sourceOriginalProbeActiveCellsA434
      m P V ν (hA ν) xi).Nonempty)
    (hActiveB : (sourceOriginalProbeActiveCellsB434
      m P V ν (hB ν) xi).Nonempty) :
    ∃ z : SourceOriginalTrueFiveIndex434 G m Q,
      z.1 = ν ∧ z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Q P V hA hB xi := by
  classical
  obtain ⟨jA,hjA⟩ := hActiveA
  obtain ⟨jB,hjB⟩ := hActiveB
  obtain ⟨χ,hχ⟩ :=
    source_original_true_primitive_family_nonempty434 Q hQ
  let z : SourceOriginalTrueFiveIndex434 G m Q :=
    ⟨ν,((jA,χ),(jB,χ))⟩
  refine ⟨z,rfl,?_⟩
  let C := sourceOriginalActualPrimitiveCharacters434 Q
  let Patterns := sourceOriginalTwoBlockProbePatterns434
    blockA blockB m
  let AA := fun ν' : SourceOriginalProbePattern434 G m =>
    sourceOriginalProbeActiveCellsA434 m P V ν' (hA ν') xi
  let BB := fun ν' : SourceOriginalProbePattern434 G m =>
    sourceOriginalProbeActiveCellsB434 m P V ν' (hB ν') xi
  have hmem : z ∈ Patterns.sigma (fun ν' =>
      ((AA ν').product C).product ((BB ν').product C)) := by
    apply Finset.mem_sigma.mpr
    constructor
    · exact hν
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_product.mpr ⟨hjA,hχ⟩,
        Finset.mem_product.mpr ⟨hjB,hχ⟩⟩
  simpa only [Patterns,AA,BB,C,
    sourceOriginalProbeExpandedFamily434,
    sourceOriginalActualFourIndexFamily434] using hmem
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueRetargetActiveCellMode -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- One ACTUAL source03 ν/primitive-character five-index mode
already present in the authentic expanded family gives a real
five-index member for EVERY other actually retained output
GLOBAL jA/jB cell pair of the SAME ν, keeping the original
primitive Dirichlet conductor and character indices.
No fictional characters or independent source comparisons
are introduced; nonempty primitive family comes from z0. -/
theorem source_original_true_retarget_active_global_cell434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi : ℝ) (z0 : SourceOriginalTrueFiveIndex434 G m Q)
    (hz0 : z0 ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi)
    (jA jB : ℤ)
    (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
      m P V z0.1 (hA z0.1) xi)
    (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
      m P V z0.1 (hB z0.1) xi) :
    let z : SourceOriginalTrueFiveIndex434 G m Q :=
      ⟨z0.1, ((jA,z0.2.1.2),(jB,z0.2.2.2))⟩
    z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Q P V hA hB xi := by
  classical
  let C := sourceOriginalActualPrimitiveCharacters434 Q
  let Patterns := sourceOriginalTwoBlockProbePatterns434
    blockA blockB m
  let AA := fun ν : SourceOriginalProbePattern434 G m =>
    sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi
  let BB := fun ν : SourceOriginalProbePattern434 G m =>
    sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi
  have hzSigma :
      z0 ∈ Patterns.sigma (fun ν =>
        ((AA ν).product C).product ((BB ν).product C)) := by
    simpa only [Patterns,AA,BB,C,
      sourceOriginalProbeExpandedFamily434,
      sourceOriginalActualFourIndexFamily434] using hz0
  have hm0 := Finset.mem_sigma.mp hzSigma
  have hpair := Finset.mem_product.mp hm0.2
  have hcharA : z0.2.1.2 ∈ C :=
    (Finset.mem_product.mp hpair.1).2
  have hcharB : z0.2.2.2 ∈ C :=
    (Finset.mem_product.mp hpair.2).2
  have hzSigma' :
      (⟨z0.1, ((jA,z0.2.1.2),(jB,z0.2.2.2))⟩ :
        SourceOriginalTrueFiveIndex434 G m Q) ∈
      Patterns.sigma (fun ν =>
        ((AA ν).product C).product ((BB ν).product C)) := by
    apply Finset.mem_sigma.mpr
    constructor
    · exact hm0.1
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨hjA,hcharA⟩
      · exact Finset.mem_product.mpr ⟨hjB,hcharB⟩
  simpa only [Patterns,AA,BB,C,
    sourceOriginalProbeExpandedFamily434,
    sourceOriginalActualFourIndexFamily434] using hzSigma'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueUniformMeshCellCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- An EXPLICIT polynomial bound for the EXACT number of
true source03 source-B/target-A GLOBAL cell pairs at the
CANONICAL uniform original Mellin mesh. The result is NOT
a bound for arbitrarily tiny widths; the chosen mesh
h=L^(-(Bmaj+4*Cq+C4))/2 is essential.
With at most M original ν mark slots, and real prime upper
bound exp(L^d), Nν <= (2*M*L^(d+E)+2)^2.
No synthetic assumption on the cell cardinality. -/
theorem source_original_true_uniform_mesh_global_cell_count434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (Cq C4 : ℕ) (L d Bmaj M : ℝ)
    (hL : 1 ≤ L) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hCount : ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) h
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) h
    ((CB.product CA).card:ℝ) ≤
      (2*M*L^(d+E)+2)^2 := by
  classical
  let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) h
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) h
  have hLpos : 0 < L := by linarith
  obtain ⟨hh,_,hinv⟩ := source_original_uniform_mellin_mesh_identity434
    Cq C4 L Bmaj hL
  have hmesh : 0 < h := hh
  have hinv' : h⁻¹ = 2*L^E := hinv
  let U : ℝ := 2*M*L^(d+E)+2
  have hDpow : 0 ≤ L^d := Real.rpow_nonneg (by linarith) _
  have hEpow : 0 ≤ L^E := Real.rpow_nonneg (by linarith) _
  have hDE : L^d * L^E = L^(d+E) := (Real.rpow_add hLpos d E).symm
  have hnA : (Fintype.card ν.1:ℝ) ≤ M := by
    have hn := Nat.cast_nonneg (α:=ℝ) (Fintype.card ν.2)
    rw [Nat.cast_add] at hCount
    linarith
  have hnB : (Fintype.card ν.2:ℝ) ≤ M := by
    have hn := Nat.cast_nonneg (α:=ℝ) (Fintype.card ν.1)
    rw [Nat.cast_add] at hCount
    linarith
  have hAupper : ((Fintype.card ν.1:ℝ)*L^d)/h+2 ≤ U := by
    dsimp only [U]
    rw [div_eq_mul_inv,hinv']
    rw [← hDE]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnA)
      (mul_nonneg hDpow hEpow)]
  have hBupper : ((Fintype.card ν.2:ℝ)*L^d)/h+2 ≤ U := by
    dsimp only [U]
    rw [div_eq_mul_inv,hinv']
    rw [← hDE]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnB)
      (mul_nonneg hDpow hEpow)]
  have hCell := source_original_true_global_cell_pair_real_count434
    m ν P L d h h hL hh hh hPrimeA hPrimeB
  have hUnn : 0 ≤ U := by dsimp [U];positivity
  have hFactorB : 0 ≤ ((Fintype.card ν.2:ℝ)*L^d)/h+2 := by
    positivity
  have hProduct :
    (((Fintype.card ν.2:ℝ)*L^d)/h+2) *
      (((Fintype.card ν.1:ℝ)*L^d)/h+2) ≤ U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hBupper hAupper
        (by positivity) hUnn
      _ = U^2 := by ring
  exact hCell.trans hProduct
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueUniformMeshMinorCountAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact absorption of the TRUE SOURCE03 all-active ν
GLOBAL-cell-count penalty. At the canonical mesh,
Nν ≤ (2*M*L^(d+E)+2)^2, and the original source
scale satisfies 16(M+1)≤L. Hence Nν is polynomial
with exponent at most 2*(d+E+1), and the true C6
8000 factor costs at most 72000 L^-Bout when
Bgoal≥Bout+2*(d+E+1). Unlike a claim for arbitrary
tiny cell widths, the mesh and label-number
restriction are mathematically necessary. -/
theorem source_original_true_uniform_mesh_minor_count_absorb434
    (L d E M N Bout Bgoal : ℝ)
    (hL : 16*(M+1) ≤ L) (hM : 0 ≤ M)
    (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hN : 0 ≤ N)
    (hCell : N ≤ (2*M*L^(d+E)+2)^2)
    (hSaving : Bout+2*(d+E+1) ≤ Bgoal) :
    N*(8000*L^(-Bgoal)) ≤ 72000*L^(-Bout) := by
  have hLone : 1 ≤ L := by nlinarith [hL,hM]
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hMbound : 2*M ≤ L := by nlinarith [hL,hM]
  let T : ℝ := L^(d+E+1)
  have hDE : 0 ≤ L^(d+E) := Real.rpow_nonneg hLnn _
  have hExpPos : 0 ≤ d+E+1 := by linarith
  have hTge : 1 ≤ T := Real.one_le_rpow hLone hExpPos
  have hTpos : 0 < T := by linarith
  have hPower : L*L^(d+E)=T := by
    calc
      L*L^(d+E) = L^(1:ℝ)*L^(d+E) := by rw [Real.rpow_one]
      _ = L^((1:ℝ)+(d+E)) := by
        exact (Real.rpow_add hLpos (1:ℝ) (d+E)).symm
      _ = T := by dsimp only [T];congr 1;ring
  have hFirst : 2*M*L^(d+E) ≤ T := by
    calc
      _ ≤ L*L^(d+E) :=
        mul_le_mul_of_nonneg_right hMbound hDE
      _ = T := hPower
  have hRnn : 0 ≤ 2*M*L^(d+E)+2 := by positivity
  have hRle : 2*M*L^(d+E)+2 ≤ 3*T := by
    linarith [hFirst,hTge]
  have hSquare : N ≤ 9*T^2 := by
    calc
      _ ≤ (2*M*L^(d+E)+2)^2 := hCell
      _ ≤ (3*T)^2 := pow_le_pow_left₀ hRnn hRle 2
      _ = 9*T^2 := by ring
  have hT2 : T^2 = L^(2*(d+E+1)) := by
    dsimp only [T]
    calc
      (L^(d+E+1))^2 = (L^(d+E+1))^(2:ℝ) :=
        (Real.rpow_natCast (L^(d+E+1)) 2).symm
      _ = L^((d+E+1)*2) :=
        (Real.rpow_mul hLnn (d+E+1) (2:ℝ)).symm
      _ = L^(2*(d+E+1)) := by ring
  have hExponent : 2*(d+E+1)-Bgoal ≤ -Bout := by
    linarith [hSaving]
  have hExpBound : L^(2*(d+E+1)-Bgoal) ≤ L^(-Bout) :=
    Real.rpow_le_rpow_of_exponent_le hLone hExponent
  have hDropNN : 0 ≤ L^(-Bgoal) := Real.rpow_nonneg hLnn _
  calc
    _ = 8000*(N*L^(-Bgoal)) := by ring
    _ ≤ 8000*(9*T^2*L^(-Bgoal)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hSquare hDropNN
    _ = 72000*L^(2*(d+E+1)-Bgoal) := by
      rw [hT2,sub_eq_add_neg,Real.rpow_add hLpos]
      ring
    _ ≤ 72000*L^(-Bout) :=
      mul_le_mul_of_nonneg_left hExpBound (by norm_num)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueUniformMeshNuPhysicalBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The exact SOURCE03 original ν-physical full-residual
major+minor+discarded budget at the certified CANONICAL
uniform Mellin log-mesh. Both the true all-active Nν
GLOBAL pair count and the discarded cell event are
absorbed at ONCE; no synthetic analytic loss assumption.
Major eps² is retained unaltered as proved by C191.
At h=L^-E/2 and xi=L^(-(2 Bmaj+d+E))/(16(M+1)):
 2*(2*(eps²+Nν*8000 L^-Bgoal)+Cgeo)
 ≤ 2*(2*(eps²+72000 L^-Bout)+L^-2Bmaj).
All exponent conditions match SOURCE03 canonical
retention/mesh schedule exactly. -/
theorem source_original_true_uniform_mesh_nu_physical_budget434
    (Cq C4 CxiNat nA nB : ℕ)
    (L Bmaj d M N Bout Bgoal eps : ℝ)
    (hBmaj : 0 ≤ Bmaj) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hL : 16*(M+1) ≤ L)
    (hCount : ((nA+nB:ℕ):ℝ) ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hN : 0 ≤ N)
    (hCell :
      N ≤ (2*M*L^(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ))))+2)^2)
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
    let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    let xi : ℝ := L^(-(2*Bmaj+d+E))/(16*(M+1))
    let Cgeo : ℝ :=
      2*((((nA:ℝ)*L^d)/h + ((nB:ℝ)*L^d)/h)+4)*xi
    2*(2*(eps^2+N*(8000*L^(-Bgoal)))+Cgeo) ≤
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) := by
  let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  let xi : ℝ := L^(-(2*Bmaj+d+E))/(16*(M+1))
  let Cgeo : ℝ :=
    2*((((nA:ℝ)*L^d)/h+((nB:ℝ)*L^d)/h)+4)*xi
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hBoundCount := source_original_true_uniform_mesh_minor_count_absorb434
    L d E M N Bout Bgoal hL hM hd hE hN
    (by simpa only [E] using hCell)
    (by simpa only [E] using hMinorExponent)
  have hSchedule := source_original_uniform_mellin_full_parameter_schedule434
    Cq C4 CxiNat nA nB L Bmaj d M
    hBmaj hd hM hL hCount hXiExponent
  obtain ⟨_,_,_,_,hDrop⟩ := hSchedule
  have hDropped : Cgeo ≤ L^(-(2*Bmaj)) := by
    simpa only [Cgeo,E,h,xi] using hDrop
  dsimp only [E,h,xi,Cgeo]
  linarith [hBoundCount,hDropped]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueUniformMeshActualNuBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The true ORIGINAL ν-dependent SOURCE-B/TARGET-A attainable
GLOBAL cell pair count and discarded-cell probability cost
are BOTH swallowed by the canonical Mellin mesh and exact
retention schedule, in the FULL C191 + C6 + discarded
signed residual coefficient. No hCellCount or hCgeo assumption
is introduced: actual labelled prime supports, their TRUE
upper bounds, mark counts, and source03 mesh are used.
For nA+nB≤M and 16(M+1)≤L the original bound becomes
  2*(2*(epsC191²+72000 L^-Bout)+L^(-(2 Bmaj))).
This is numerical loss absorption, not ν/four-sign gluing. -/
theorem source_original_true_uniform_mesh_ACTUAL_nu_budget434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (Cq C4 CxiNat : ℕ)
    (L Bmaj d M Bout Bgoal eps : ℝ)
    (hBmaj : 0 ≤ Bmaj) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hL : 16*(M+1) ≤ L)
    (hCount :
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
    let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
    let h : ℝ := L^(-E)/2
    let xi : ℝ := L^(-(2*Bmaj+d+E))/(16*(M+1))
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) h
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) h
    let Cgeo : ℝ :=
      2*((((Fintype.card ν.1:ℝ)*L^d)/h +
          ((Fintype.card ν.2:ℝ)*L^d)/h)+4)*xi
    2*(2*(eps^2+
        ((CB.product CA).card:ℝ)*(8000*L^(-Bgoal)))+Cgeo) ≤
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) := by
  classical
  let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  let xi : ℝ := L^(-(2*Bmaj+d+E))/(16*(M+1))
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) h
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) h
  have hCells := source_original_true_uniform_mesh_global_cell_count434
    m ν P Cq C4 L d Bmaj M (by linarith : 1 ≤ L)
    hd hM hCount hPrimeA hPrimeB
  have hBudget := source_original_true_uniform_mesh_nu_physical_budget434
    Cq C4 CxiNat (Fintype.card ν.1) (Fintype.card ν.2)
    L Bmaj d M ((CB.product CA).card:ℝ)
    Bout Bgoal eps hBmaj hd hM hL hCount hXiExponent
    (Nat.cast_nonneg _) hCells hMinorExponent
  simpa only [E,h,xi,CB,CA] using hBudget
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTwoGlobalLiteralCellProductCap -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- ORIGINAL half-open GLOBAL log cells give the needed joint
upper product scale exactly, with no hypothetical source03
dyadic product cap R. Any two positive original arithmetic
products n,m in cells jA,jB satisfy
  n*m <= exp((jA+1)*hA+(jB+1)*hB).
No upper bound on the *number* of prime tuples is introduced.
This is the precise missing geometric input for the full
rational + slowly varying Mellin major-arc C164 theorem. -/
theorem source_original_two_global_literal_cell_product_cap434
    (hA hB : ℝ) (jA jB : ℤ)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA n)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB m) :
    (((n*m:ℕ):ℝ) ≤
      Real.exp (((jA:ℝ)+1)*hA + ((jB:ℝ)+1)*hB)) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hnmR : (0:ℝ) < (((n*m:ℕ):ℝ)) := by
    exact_mod_cast Nat.mul_pos hn hm
  have hLogMul :
      Real.log (((n*m:ℕ):ℝ)) =
      Real.log (n:ℝ) + Real.log (m:ℝ) := by
    rw [Nat.cast_mul]
    exact Real.log_mul (ne_of_gt hnR) (ne_of_gt hmR)
  have hU :
      Real.log (((n*m:ℕ):ℝ)) <
        ((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB := by
    dsimp only [sourceOriginalLiteralLogCell434] at hCellA hCellB
    rw [hLogMul]
    linarith [hCellA.2,hCellB.2]
  calc
    (((n*m:ℕ):ℝ)) =
        Real.exp (Real.log (((n*m:ℕ):ℝ))) :=
          (Real.exp_log hnmR).symm
    _ ≤ Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) :=
      Real.exp_le_exp.mpr hU.le
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTwoGlobalPhysicalCellCap -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- A TRUE original source03 labelled product of BIG prime
marks is positive. This is the exact positivity prerequisite
for the logarithm identities; numerical prime repetitions
at different labelled slots are allowed. -/
theorem source_original_gram_physical_prime_product_pos434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (hPrime : ∀ i p, p ∈ S i → p.Prime)
    (q : SourceOriginalGramPrimeTuple434 S) :
    0 < sourceOriginalGramPrimeProduct434 S q := by
  unfold sourceOriginalGramPrimeProduct434
  apply Finset.prod_pos
  intro i hi
  exact (hPrime i (q i).val (q i).property).pos

/-- Every actual pair of SOURCE03 independently labelled physical
GLOBAL A/B prime tuples within given retained cells obeys
the SAME explicit joint product cap Rcell. No externally
supplied hUpper is needed for the rational + Mellin
major-arc comparison. Exactly the two original source03
polynomially indexed prime supports are retained. -/
theorem source_original_physical_two_global_cell_product_cap434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (hPrimeA : ∀ i p, p ∈ SA i → p.Prime)
    (hPrimeB : ∀ i p, p ∈ SB i → p.Prime)
    (hA hB : ℝ) (jA jB : ℤ)
    (pA : SourceOriginalGramPrimeTuple434 SA)
    (pB : SourceOriginalGramPrimeTuple434 SB)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA
       (sourceOriginalGramPrimeProduct434 SA pA))
    (hCellB : sourceOriginalLiteralLogCell434 hB jB
       (sourceOriginalGramPrimeProduct434 SB pB)) :
    (((sourceOriginalGramPrimeProduct434 SA pA *
       sourceOriginalGramPrimeProduct434 SB pB):ℕ):ℝ) ≤
       Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) := by
  have hpA : 0 < sourceOriginalGramPrimeProduct434 SA pA :=
    source_original_gram_physical_prime_product_pos434 SA hPrimeA pA
  have hpB : 0 < sourceOriginalGramPrimeProduct434 SB pB :=
    source_original_gram_physical_prime_product_pos434 SB hPrimeB pB
  exact source_original_two_global_literal_cell_product_cap434
    hA hB jA jB
    (sourceOriginalGramPrimeProduct434 SA pA)
    (sourceOriginalGramPrimeProduct434 SB pB)
    hpA hpB hCellA hCellB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLocalCellDyadCap -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- ORIGINAL two-GLOBAL physical product-log cells admit a sharp
scale bound in terms of the ACTUAL target product X_A X_B
rather than the coarse BIG-group cutoff:
 Rcell=exp((jA+1)hA+(jB+1)hB)
       <= X_A X_B * exp(hA+hB).
The original half-open logarithmic cell constraints are
retained. No unproved Hprime comparison is assumed. -/
theorem source_original_two_global_local_cell_target_cap434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB) :
    Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) ≤
        ((XA*XB:ℕ):ℝ)*Real.exp (hA+hB) := by
  have hxA : (0:ℝ) < XA := by exact_mod_cast hXAp
  have hxB : (0:ℝ) < XB := by exact_mod_cast hXBp
  have hlog :
      Real.log ((XA*XB:ℕ):ℝ) =
        Real.log (XA:ℝ)+Real.log (XB:ℝ) := by
    rw [Nat.cast_mul]
    exact Real.log_mul hxA.ne' hxB.ne'
  have hBound :
      ((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB ≤
        Real.log ((XA*XB:ℕ):ℝ)+(hA+hB) := by
    dsimp only [sourceOriginalLiteralLogCell434] at hCellA hCellB
    rw [hlog]
    nlinarith [hCellA.1,hCellB.1]
  calc
    _ ≤ Real.exp (Real.log ((XA*XB:ℕ):ℝ)+(hA+hB)) :=
      Real.exp_le_exp.mpr hBound
    _ = ((XA*XB:ℕ):ℝ)*Real.exp (hA+hB) := by
      rw [Real.exp_add]
      have hProduct : (0:ℝ) < ((XA*XB:ℕ):ℝ) := by
        exact_mod_cast Nat.mul_pos hXAp hXBp
      rw [Real.exp_log hProduct]

/-- SOURCE03 ORIGINAL dyadic localization X_A∈[U,2U],
X_B∈[V,2V] implies the genuine local GLOBAL cell product
scale Rcell <= 4*exp(hA+hB)*Hprime,
Hprime=U*V, with NO global exp(m*L^d) loss.
This is the exact arithmetic bridge required to match the
major-arc Dirichlet radius |beta|<=L^Carc/Hprime to the true
source03 primitive frame slow-oscillation estimate. -/
theorem source_original_two_global_local_cell_dyad_cap434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V : ℝ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hXA : (XA:ℝ) ≤ 2*U)
    (hXB : (XB:ℝ) ≤ 2*V)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB) :
    Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) ≤
        4*Real.exp (hA+hB)*(U*V) := by
  have hLocal := source_original_two_global_local_cell_target_cap434
    hA hB jA jB XA XB hXAp hXBp hCellA hCellB
  have hxB : (0:ℝ) ≤ XB := by exact_mod_cast (Nat.zero_le XB)
  have hProd : ((XA*XB:ℕ):ℝ) ≤ 4*(U*V) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2*U)*(2*V) :=
        mul_le_mul hXA hXB hxB (by positivity)
      _ = 4*(U*V) := by ring
  have hexp : 0 ≤ Real.exp (hA+hB) :=
    (Real.exp_pos _).le
  calc
    _ ≤ ((XA*XB:ℕ):ℝ)*Real.exp (hA+hB) := hLocal
    _ ≤ (4*(U*V))*Real.exp (hA+hB) :=
      mul_le_mul_of_nonneg_right hProd hexp
    _ = 4*Real.exp (hA+hB)*(U*V) := by ring
end Green64Analytic.CorrelationSquare

end

