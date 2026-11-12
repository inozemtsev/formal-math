module

public import Green64.Library.Correlation.Part036
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part032
public import Green64.Library.Weights.Part047
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Green64.Library.Weights.Part001
public import Green64.Library.Weights.Part045
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part016
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.Part049
public import Green64.Library.Weights.Part015
public import Green64.Library.Analysis.Estimates.Part005
public import Green64.Library.Weights.Part013
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Correlation / Part037

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSource03TrueNuPhysicalMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The true SOURCE03 ν-selected A/B BIG prime-label physical
minor-circle bilinear sum on the actual shifted integer dyad
windows has the C6 squared-L² log-power saving.
Unlike previous C280 coefficient-only statement, this is the
literal physical PRIME-TUPLE sum over unrestricted
mark-dependent tests and genuinely grouped harmonic measures.
The equality to C6 atoms is proved by finite Fubini/reindexing,
not asserted. Both blocks use original BIG groups; the
original group disjointness and Dirichlet/boundary assumptions
remain explicit. NOT YET the signed RAW-minus-Knu residual. -/
theorem source_original_source03_true_nu_two_big_physical_minor_L2_log_power434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : A => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : B => d.Tb z.val.1) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(∑ vA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
        (∑ vB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (((a:ℝ)/(r:ℝ)+beta0)*
                  ((sourceOriginalGramPrimeProduct434 SB vB:ℕ):ℝ))
                ((sourceOriginalGramPrimeProduct434 SA vA:ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  have hMinor :=
    source_original_source03_true_nu_two_big_minor_L2_log_power434
      cfg x L Y Hprime d sep blockA blockB hDisjoint
      m hm A B hPattern fA fB
      M N P Q hM hN a r beta0 hr hcop hbeta hP hQ
      D Bsave hL hR hNlarge hMlarge hMNlarge
      C hExponent hSaving
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  have hFub :=
    source_original_physical_two_shifted_window_fubini434
      SA muA SB muB fA fB M N P Q
      (fun n m => Green64SourceC6.integerPhase
        (((a:ℝ)/(r:ℝ)+beta0)*(m:ℝ)) (n:ℤ))
  dsimp only at hFub
  dsimp only
  rw [hFub]
  exact hMinor
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedRawPhysicalMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The actual ORIGINAL SOURCE03 signed RAW Fourier component,
not a comparison Knu: for one true ν-pattern, both independent
physical harmonic prime tuples, unrestricted mark-sensitive
complex source/target tests, literal product-window masks,
and original -(-1)^(|A|+|B|) inclusion-exclusion coefficient.
The already independently proved C6 integer bilinear minor
log-power saving is transported to the EXACT Fourier frequency
-k theta. Rational approximation and every minor C6 side
condition are EXPLICIT, not manufactured by the phase identity.
This estimates RAW on the true individual ν minor branch; it
does NOT claim any saving of RAW inside a major arc. -/
theorem source_original_true_signed_raw_physical_minor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (ν : SourceOriginalProbePattern434 β m)
    (hPattern : ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : ν.1 => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : ν.2 => d.Tb z.val.1) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (∑ vA : SourceOriginalGramPrimeTuple434 SA,
        if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
          (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
          (∑ vB : SourceOriginalGramPrimeTuple434 SB,
            if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
              (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA vA *
                   sourceOriginalGramPrimeProduct434 SB vB):ℕ):ℤ)
            else 0)
        else 0)‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  have hRaw :=
    source_original_source03_true_nu_two_big_physical_minor_L2_log_power434
      cfg x L Y Hprime d sep
      blockA blockB hDisjoint m hm ν.1 ν.2 hPattern
      fA fB M N P Q hM hN a r beta0 hr hcop hbeta
      hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge
      C hExponent hSaving
  have hPhase :=
    source_original_physical_minor_fourier_phase_identity434
      SA muA SB muB fA fB AW BW theta k a r beta0 hApprox
  dsimp only at hRaw
  rw [hPhase] at hRaw
  dsimp only
  rw [norm_mul]
  have hSign : ‖(-((-1:ℂ)^(ν.1.card+ν.2.card)))‖ = 1 := by
    simp
  rw [hSign,one_mul]
  exact hRaw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedRawMellinWeightedMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- Genuine signed SOURCE03 two-BIG RAW C6 minor with the
full original Mellin factor at D_A*D_B and exact -k theta,
for every real Mellin frequency ζ. The two original genuine
prime products are positive and the Mellin twist factors into
unit-modulus endpoint test multipliers. Hence the true
weighted L2 energies, arbitrary mark-dependent complex tests,
window masks, and the C6 log-power saving are ALL unchanged.
All source admissibility and rational minor C6 hypotheses
remain explicit. No claim about Knu/RAW cancellation on major
arcs or the full Green64 theorem. -/
theorem source_original_true_signed_raw_mellin_physical_minor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (ν : SourceOriginalProbePattern434 β m)
    (hPattern : ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (ζ : ℝ)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : ν.1 => d.Tb z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : ν.2 => d.Tb z.val.1) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (∑ vA : SourceOriginalGramPrimeTuple434 SA,
        if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
          (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
          (∑ vB : SourceOriginalGramPrimeTuple434 SB,
            if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
              (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA vA *
                   sourceOriginalGramPrimeProduct434 SB vB):ℕ):ℤ) *
              sourceOriginalPureMellinPhase434 ζ
                (sourceOriginalGramPrimeProduct434 SA vA *
                 sourceOriginalGramPrimeProduct434 SB vB)
            else 0)
        else 0)‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => (sourceOriginalGramPrimeMass434 SA muA a:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => (sourceOriginalGramPrimeMass434 SB muB b:ℂ)
  let fAz : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun a => fA a * sourceOriginalPureMellinPhase434 ζ (pa a)
  let fBz : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun b => fB b * sourceOriginalPureMellinPhase434 ζ (pb b)
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  let EA : ℝ := ∑ a : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA a * ‖fA a‖^2
  let EB : ℝ := ∑ b : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB b * ‖fB b‖^2
  have hPA (a : SourceOriginalGramPrimeTuple434 SA) :
      0 < pa a := by
    unfold pa sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (d.hTbPrime z.val.1 (a z).val (a z).property).pos
  have hPB (b : SourceOriginalGramPrimeTuple434 SB) :
      0 < pb b := by
    unfold pb sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (d.hTbPrime z.val.1 (b z).val (b z).property).pos
  have hEs :=
    source_original_true_nu_mellin_two_energy_eq434
      m ν d.Tb
      (fun a : SourceOriginalGramPrimeTuple434 SA =>
        sourceOriginalGramPrimeMass434 SA muA a)
      (fun b : SourceOriginalGramPrimeTuple434 SB =>
        sourceOriginalGramPrimeMass434 SB muB b)
      ζ fA fB
  have hEA :
      (∑ a : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA a*‖fAz a‖^2) = EA :=
    hEs.1
  have hEB :
      (∑ b : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB b*‖fBz b‖^2) = EB :=
    hEs.2
  have hC6 := source_original_true_signed_raw_physical_minor434
    cfg x L Y Hprime d sep
    blockA blockB hDisjoint m hm ν hPattern
    fAz fBz M N P Q hM hN
    a r beta0 theta k hApprox
    hr hcop hbeta hP hQ D Bsave hL hR
    hNlarge hMlarge hMNlarge
    C hExponent hSaving
  dsimp only at hC6
  rw [hEA,hEB] at hC6
  have hIdentity :
      (∑ a : SourceOriginalGramPrimeTuple434 SA,
        if pa a ∈ AW then wA a*fAz a*
          (∑ b : SourceOriginalGramPrimeTuple434 SB,
            if pb b ∈ BW then
              wB b*fBz b*
              Green64SourceC6.integerPhase (-(k:ℝ)*theta)
                (((pa a*pb b:ℕ):ℤ))
            else 0)
        else 0) =
      (∑ a : SourceOriginalGramPrimeTuple434 SA,
        if pa a ∈ AW then wA a*fA a*
          (∑ b : SourceOriginalGramPrimeTuple434 SB,
            if pb b ∈ BW then
              wB b*fB b*
              Green64SourceC6.integerPhase (-(k:ℝ)*theta)
                (((pa a*pb b:ℕ):ℤ)) *
              sourceOriginalPureMellinPhase434 ζ (pa a*pb b)
            else 0)
        else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases haw : pa a ∈ AW
    · simp only [if_pos haw]
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbw : pb b ∈ BW
      · simp only [if_pos hbw]
        rw [source_original_pure_mellin_product_factor434
          ζ (pa a) (pb b) (hPA a) (hPB b)]
        dsimp only [fAz,fBz]
        ring
      · simp only [if_neg hbw]
        ring
    · simp only [if_neg haw]
  dsimp only
  change
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (∑ a : SourceOriginalGramPrimeTuple434 SA,
        if pa a ∈ AW then wA a*fA a*
          (∑ b : SourceOriginalGramPrimeTuple434 SB,
            if pb b ∈ BW then
              wB b*fB b*
              Green64SourceC6.integerPhase (-(k:ℝ)*theta)
                (((pa a*pb b:ℕ):ℤ)) *
              sourceOriginalPureMellinPhase434 ζ (pa a*pb b)
            else 0)
        else 0)‖^2 ≤
      125*(EA*EB)*L^(-Bsave)
  rw [← hIdentity]
  exact hC6
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAuxExpectationFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- EXACT source03 original dependent ν auxiliary BIG
prime draw expectation = a joint physical A_ν/B_ν
Gram-tuple expectation. The test K sees ALL original
auxiliary marked-prime slots, with the inverse genuine
prime tuple equivalence (not just integer products).
The true original law 1/(p V_g), first/second
labelled prime products and ν support are preserved.
This is an actual algebraic probability reindexing,
NOT an independent artificial copy of the original data. -/
theorem source_original_true_aux_expectation_fubini434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (K : (SourceOriginalProbeAuxIndex434 m ν → ℕ) → ℂ) :
    (∑ a ∈ Fintype.piFinset
        (sourceOriginalProbeAuxPrimeSets434 m ν P),
      (sourceSharedLaw434
        (fun i => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m ν V i)) a:ℂ)*K a) =
    ∑ ab : SourceOriginalGramPrimeTuple434
          (fun i : ν.1 => P i.val.1) ×
        SourceOriginalGramPrimeTuple434
          (fun i : ν.2 => P i.val.1),
      ((sourceOriginalGramPrimeMass434
         (fun i : ν.1 => P i.val.1)
         (fun i p => (1/(p:ℝ))/(V i.val.1)) ab.1 *
        sourceOriginalGramPrimeMass434
         (fun i : ν.2 => P i.val.1)
         (fun i p => (1/(p:ℝ))/(V i.val.1)) ab.2 : ℝ):ℂ) *
      K (fun i =>
        ((sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P).symm ab i).val) := by
  classical
  let F : SourceOriginalProbeAuxIndex434 m ν → Finset ℕ :=
    sourceOriginalProbeAuxPrimeSets434 m ν P
  let X := SourceOriginalGramPrimeTuple434 (fun i : ν.1 => P i.val.1)
  let Y := SourceOriginalGramPrimeTuple434 (fun i : ν.2 => P i.val.1)
  let E : ((i : SourceOriginalProbeAuxIndex434 m ν) → {p : ℕ // p ∈ F i}) ≃
      X × Y := sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P
  let Φ : (↑(Fintype.piFinset F)) ≃ X × Y :=
    (sourceFiniteListFamilyEquiv434 F).trans E
  let w : SourceOriginalProbeAuxIndex434 m ν → ℕ → ℝ :=
    fun i p => sourcePrimeSharedAtom434
      (sourceOriginalProbeAuxV434 m ν V i) p
  let wa : ν.1 → ℕ → ℝ :=
    fun i p => (1/(p:ℝ))/(V i.val.1)
  let wb : ν.2 → ℕ → ℝ :=
    fun i p => (1/(p:ℝ))/(V i.val.1)
  let SA : ν.1 → Finset ℕ := fun i => P i.val.1
  let SB : ν.2 → Finset ℕ := fun i => P i.val.1
  have hM (a : ↑(Fintype.piFinset F)) :
      sourceSharedLaw434 w a.val =
       sourceOriginalGramPrimeMass434 SA wa (Φ a).1 *
       sourceOriginalGramPrimeMass434 SB wb (Φ a).2 := by
    have hh := source_original_true_aux_split_mass434 m ν P V
      ((sourceFiniteListFamilyEquiv434 F) a)
    change sourceSharedLaw434 w a.val =
       sourceOriginalGramPrimeMass434 SA wa (Φ a).1 *
       sourceOriginalGramPrimeMass434 SB wb (Φ a).2 at hh
    exact hh
  have hK (a : ↑(Fintype.piFinset F)) :
      (fun i => ((E.symm (Φ a)) i).val) = a.val := by
    change (fun i => ((E.symm (E ((sourceFiniteListFamilyEquiv434 F) a))) i).val) = a.val
    simp only [Equiv.symm_apply_apply]
    rfl
  have hPoint (a : ↑(Fintype.piFinset F)) :
      (sourceSharedLaw434 w a.val:ℂ)*K a.val =
      ((sourceOriginalGramPrimeMass434 SA wa (Φ a).1 *
         sourceOriginalGramPrimeMass434 SB wb (Φ a).2 :ℝ):ℂ) *
        K (fun i => ((E.symm (Φ a)) i).val) := by
    rw [hK a,hM a]
  have hFub :=
    Fintype.sum_equiv Φ
      (fun a : ↑(Fintype.piFinset F) =>
        (sourceSharedLaw434 w a.val:ℂ)*K a.val)
      (fun ab : X × Y =>
        ((sourceOriginalGramPrimeMass434 SA wa ab.1 *
           sourceOriginalGramPrimeMass434 SB wb ab.2:ℝ):ℂ) *
        K (fun i => ((E.symm ab) i).val))
      hPoint
  calc
    _ = ∑ a : ↑(Fintype.piFinset F),
        (sourceSharedLaw434 w a.val:ℂ)*K a.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ ab : X × Y,
        ((sourceOriginalGramPrimeMass434 SA wa ab.1 *
           sourceOriginalGramPrimeMass434 SB wb ab.2 :ℝ):ℂ) *
        K (fun i => ((E.symm ab) i).val) := hFub
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCircleDyadScale -/

section

open Filter Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- SOURCE03 minor circle's TRUE four-term spectral saving
implies precisely all three C6 integer-window scale
conditions, provided the actual half-open product cells
have been covered by dyads M>=U1, N>=U2.
No artificial upper bound r<=L^Carc is required. -/
theorem source_original_true_circle_spectral_to_C6_scales434
    (U1 U2 L D : ℝ) (M N r : ℕ)
    (hU1 : 0 < U1) (hU2 : 0 < U2)
    (hL : 1 ≤ L) (hr : 0 < r)
    (hMA : U1 ≤ (M:ℝ)) (hNB : U2 ≤ (N:ℝ))
    (hSpectral :
       1/U2+1/(r:ℝ)+Real.log (2*(r:ℝ))/U1+
       (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) ≤ 1/L^D) :
    L^D ≤ (r:ℝ) ∧ L^D ≤ (N:ℝ) ∧
    L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ) ∧
    L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
      (M:ℝ)*(N:ℝ) := by
  have hLp : 0 < L := by linarith
  have hE : 0 < L^D := Real.rpow_pos_of_pos hLp D
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hrge : (1:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr.ne')
  have hLog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  have hRterm : 0 ≤ 1/(r:ℝ) := by positivity
  have hNterm : 0 ≤ 1/U2 := by positivity
  have hMterm : 0 ≤ Real.log (2*(r:ℝ))/U1 :=
    div_nonneg hLog hU1.le
  have hMNterm :
     0 ≤ (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) :=
    div_nonneg (mul_nonneg hrp.le hLog)
      (mul_pos hU1 hU2).le
  have h1 : 1/(r:ℝ) ≤ 1/L^D := by linarith
  have h2 : 1/U2 ≤ 1/L^D := by linarith
  have h3 : Real.log (2*(r:ℝ))/U1 ≤ 1/L^D := by
    linarith
  have h4 : (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) ≤
      1/L^D := by linarith
  have hR : L^D ≤ (r:ℝ) := by
    have hh := (div_le_div_iff₀ hrp hE).mp h1
    nlinarith
  have hNU : L^D ≤ U2 := by
    have hh := (div_le_div_iff₀ hU2 hE).mp h2
    nlinarith
  have hMU : L^D*Real.log (2*(r:ℝ)) ≤ U1 := by
    have hh := (div_le_div_iff₀ hU1 hE).mp h3
    nlinarith
  have hMNU :
     L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ U1*U2 := by
    have hh := (div_le_div_iff₀ (mul_pos hU1 hU2) hE).mp h4
    nlinarith
  have hMN : U1*U2 ≤ (M:ℝ)*(N:ℝ) :=
    mul_le_mul hMA hNB hU2.le (by positivity)
  refine ⟨hR, hNU.trans hNB, ?_, ?_⟩
  · exact hMU.trans hMA
  · exact hMNU.trans hMN
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCircleMinorFullDyad -/

section

open Filter Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- An extra single log power absorbs the exact constant 4
from original source03 major/minor rational partition. -/
theorem source_original_circle_four_div_power_absorb434
    (L D : ℝ) (hL : 4 ≤ L) :
    4/L^(D+1) ≤ 1/L^D := by
  have hp : 0 < L := by linarith
  have hE : 0 < L^D := Real.rpow_pos_of_pos hp _
  have hE1 : 0 < L^(D+1) := Real.rpow_pos_of_pos hp _
  have hh : 4*L^D ≤ L^(D+1) := by
    rw [Real.rpow_add hp,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hL hE.le]
  apply (div_le_div_iff₀ hE1 hE).2
  nlinarith [hh]

/-- Actual original source03 rational minor-circle estimate,
converted to ALL THREE TRUE physical C6 dyad scale hypotheses.
Unlike the old r<=L^Carc lemma this has no artificial upper
denominator bound; signed frequency is exactly -k*theta. -/
theorem eventually_source_original_circle_physical_C6_scales434
    (c d A D Carc C1 C2 Chigh : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hdA : d < A) (hD : 0 ≤ D)
    (hCarc : A+(D+1) ≤ Carc) (hChigh : 0 ≤ Chigh) :
    ∀ᶠ L : ℝ in atTop,
      4 ≤ L ∧
      ∀ U1 U2 Hprime : ℝ,
        Real.exp (L^c-C1) ≤ U1 →
        Real.exp (L^c-C2) ≤ U2 →
        Hprime = U1*U2 → 0 < Hprime →
        Hprime ≤ Real.exp (Chigh*Real.log L*L^d) →
        ∀ (M N : ℕ),
          U1 ≤ (M:ℝ) → U2 ≤ (N:ℝ) →
        ∀ (theta : ℝ) (k : ℤ), k ≠ 0 →
          (theta:AddCircle (1:ℝ)) ∉ sourceCircleRationalArcs434
            (k.natAbs*Nat.ceil (L^(D+1)))
            (L^Carc/Hprime) →
          ∃ (a : ℤ) (r : ℕ),
            0 < r ∧ Int.gcd a (r:ℤ) = 1 ∧
            |-(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
            L^D ≤ (r:ℝ) ∧ L^D ≤ (N:ℝ) ∧
            L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ) ∧
            L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
              (M:ℝ)*(N:ℝ) := by
  have hCircle :=
    eventually_source_circle_minor_rational434
      c d A (D+1) Carc C1 C2 Chigh
      hc hd hdA (by linarith : 0 ≤ D+1) hCarc hChigh
  filter_upwards [hCircle,eventually_ge_atTop (4:ℝ)]
    with L hOriginal hL
  refine ⟨hL,?_⟩
  intro U1 U2 Hprime hU1 hU2 hH hHp hHhi
    M N hMA hNB theta k hk hOutside
  obtain ⟨a,r,hr,hcop,hNear,hR,hSpectrum⟩ :=
    hOriginal.2 U1 U2 Hprime hU1 hU2 hH hHp hHhi
      theta k hk hOutside
  have hU1p : 0 < U1 := (Real.exp_pos _).trans_le hU1
  have hU2p : 0 < U2 := (Real.exp_pos _).trans_le hU2
  have hExact :
      1/U2+1/(r:ℝ)+Real.log (2*(r:ℝ))/U1+
      (r:ℝ)*Real.log (2*(r:ℝ))/(U1*U2) ≤
      1/L^D := hSpectrum.trans
       (source_original_circle_four_div_power_absorb434 L D hL)
  obtain ⟨hR',hN',hM',hMN'⟩ :=
    source_original_true_circle_spectral_to_C6_scales434
      U1 U2 L D M N r hU1p hU2p (by linarith) hr
      hMA hNB hExact
  exact ⟨a,r,hr,hcop,hNear,hR',hN',hM',hMN'⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuCircleDyadicPhysical -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The ORIGINAL source03 C6 bound on genuinely ν-selected
independently labelled BIG/BIG physical marked prime tuples,
with arbitrary complex endpoint tests, is valid off the true
circle major arcs on EVERY containing dyad [M,M+P) and
[N,N+Q), P<=M, Q<=N.
The rational denominator is found by original Dirichlet circle
partition, not artificially capped by L^Carc. The endpoint
Fourier frequency has the authentic negative sign -k*theta.
Per-cell H'=U_A*U_B stays explicit because it MOVES with jA,jB.
This theorem makes no RAW-minus-Kν or Green64 claim. -/
theorem eventually_source_original_true_nu_circle_dyadic_physical434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
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
      (blockA blockB : Finset β)
      (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (A B : Finset (β × Fin m))
      (hPattern : (A,B) ∈
        sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (fA : SourceOriginalGramPrimeTuple434
        (fun z : A => d.Tb z.val.1) → ℂ)
      (fB : SourceOriginalGramPrimeTuple434
        (fun z : B => d.Tb z.val.1) → ℂ)
      (U1 U2 Hcell : ℝ)
      (hU1 : Real.exp (L^cfg.cexp-1) ≤ U1)
      (hU2 : Real.exp (L^cfg.cexp-1) ≤ U2)
      (hH : Hcell = U1*U2) (hHp : 0 < Hcell)
      (hHupper :
        Hcell ≤ Real.exp (Chigh*Real.log L*L^(1/2:ℝ)))
      (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
      (hP : P ≤ M) (hQ : Q ≤ N)
      (hCellA : U1 ≤ (M:ℝ))
      (hCellB : U2 ≤ (N:ℝ))
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
      let EA : ℝ :=
        ∑ v : SourceOriginalGramPrimeTuple434 SA,
          sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
      let EB : ℝ :=
        ∑ v : SourceOriginalGramPrimeTuple434 SB,
          sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
      ‖(∑ i ∈ Finset.range P,
        sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
        (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (-(k:ℝ)*theta)
            (((M+i)*(N+j):ℕ):ℤ)))‖^2 ≤
        125*(EA*EB)*L^(-Bsave) := by
  have hc : 0 < cfg.cexp := by
    linarith [cfg.haexp,cfg.hab,cfg.hbc]
  have hCircle := eventually_source_original_circle_physical_C6_scales434
      cfg.cexp (1/2:ℝ) Aarc D cfg.Carc 1 1 Chigh
      hc (by norm_num) hAarc hD hArc hChigh
  filter_upwards [hCircle] with L hCircleL
  intro ι β instI instDI instB instDB x Y Hprime d sep
    blockA blockB hDisjoint m hm A B hPattern fA fB
    U1 U2 Hcell hU1 hU2 hH hHp hHupper
    M N P Q hM hN hP hQ hCellA hCellB theta k hk hOutside
  dsimp only
  obtain ⟨a,r,hr,hcop,hNear,hR,hNlarge,hMlarge,hMNlarge⟩ :=
    hCircleL.2 U1 U2 Hcell hU1 hU2 hH hHp
      hHupper M N hCellA hCellB theta k hk hOutside
  let beta : ℝ := -(k:ℝ)*theta - (a:ℝ)/(r:ℝ)
  have hApprox : -(k:ℝ)*theta =
      (a:ℝ)/(r:ℝ)+beta := by
    dsimp [beta]
    ring
  have hbeta : |beta| ≤ 1/((r:ℝ)^2) := by
    simpa only [beta] using hNear
  have hBound :=
    source_original_source03_true_nu_two_big_minor_L2_log_power434
      cfg x L Y Hprime d sep
      blockA blockB hDisjoint m hm A B hPattern
      fA fB M N P Q hM hN a r beta
      hr hcop hbeta hP hQ D Bsave
      (by linarith [hCircleL.1] : 1 ≤ L)
      hR hNlarge hMlarge hMNlarge
      C hExponent hSaving
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  dsimp only at hBound
  have hPhase :
    (a:ℝ)/(r:ℝ)+beta = -(k:ℝ)*theta := hApprox.symm
  simp_rw [hPhase] at hBound
  simp_rw [source_original_C6_integer_phase_natural_product434] at hBound
  simpa only [SA,SB,muA,muB,EA,EB] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexCircleDyad -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine source03 five-index (ν,jA,χA,jB,χB) term,
for ANY of its four deterministic physical dyadic rectangles,
inherits original minor-circle C6 cancellation. The moving
Hcell=exp(jA*hA)exp(jB*hB) is CONSTRUCTED from this term.
No independent U1/U2/Hcell, no fake r<=L^Carc, and no
assumed spectral scale inequality. Signed Fourier phase
is -k*theta, tests remain arbitrarily mark-dependent. -/
theorem eventually_source_original_true_five_index_circle_dyadic434
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
      (xi : ℝ)
      (z : Σ ν : SourceOriginalProbePattern434 β m,
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) ×
        (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))))
      (hz : z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar d.Tb d.Vbig hA hB xi)
      (fA : SourceOriginalGramPrimeTuple434
        (fun t : z.1.1 => d.Tb t.val.1) → ℂ)
      (fB : SourceOriginalGramPrimeTuple434
        (fun t : z.1.2 => d.Tb t.val.1) → ℂ)
      (M N : ℕ)
      (hMchoice :
        M = Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hA z.1)) ∨
        M = 2*Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hA z.1)))
      (hNchoice :
        N = Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hB z.1)) ∨
        N = 2*Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hB z.1)))
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
      let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
        sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
      let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
        sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
      ‖(∑ i ∈ Finset.range M,
         sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
         (∑ j ∈ Finset.range N,
           sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
           Green64SourceC6.integerPhase
             (-(k:ℝ)*theta)
             (((M+i)*(N+j):ℕ):ℤ)))‖^2 ≤
         125*(EA*EB)*L^(-Bsave) := by
  let Chigh : ℝ := 2*(cfg.tmax:ℝ)*cfg.C0
  have hChigh : 0 ≤ Chigh := by
    dsimp [Chigh]
    exact mul_nonneg (by positivity) cfg.hC0
  have hCircle := eventually_source_original_true_nu_circle_dyadic_physical434
    cfg D Bsave hD C hExponent hSaving Aarc Chigh hAarc hArc hChigh
  filter_upwards [hCircle,eventually_ge_atTop (4:ℝ)] with L hCircleL hL
  intro ι β instI instDI instB instDB x Y Hprime d sep
    blockA blockB hDisjoint m Qchar hm hTbLower
    hA hB hhA hhB xi z hz fA fB
    M N hMchoice hNchoice theta k hk hOutside
  let UA : ℝ := Real.exp ((z.2.1.1:ℝ)*hA z.1)
  let UB : ℝ := Real.exp ((z.2.2.1:ℝ)*hB z.1)
  let HC : ℝ := sourceOriginalProbeTrueHprime434 m Qchar hA hB z
  change M = Nat.ceil UA ∨ M = 2*Nat.ceil UA at hMchoice
  change N = Nat.ceil UB ∨ N = 2*Nat.ceil UB at hNchoice
  obtain ⟨hU1,hU2,hH,hHupper⟩ :=
    source_original_source03_true_five_index_circle_scales434
      cfg x L Y Hprime d (by linarith) blockA blockB
      m Qchar hm hTbLower hA hB hhA hhB xi z hz
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hM0 : 0 < Nat.ceil UA := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hN0 : 0 < Nat.ceil UB := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hMp : 0 < M := by
    rcases hMchoice with h | h
    · rw [h]; exact hM0
    · rw [h]; omega
  have hNp : 0 < N := by
    rcases hNchoice with h | h
    · rw [h]; exact hN0
    · rw [h]; omega
  have hMA : UA ≤ (M:ℝ) := by
    have hh : UA ≤ (Nat.ceil UA:ℝ) := Nat.le_ceil UA
    rcases hMchoice with h | h
    · rw [h]; exact hh
    · rw [h]
      have hNonneg : (0:ℝ) ≤ (Nat.ceil UA:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hNB : UB ≤ (N:ℝ) := by
    have hh : UB ≤ (Nat.ceil UB:ℝ) := Nat.le_ceil UB
    rcases hNchoice with h | h
    · rw [h]; exact hh
    · rw [h]
      have hNonneg : (0:ℝ) ≤ (Nat.ceil UB:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hHp : 0 < HC := by
    change 0 < UA*UB
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hBound :=
    hCircleL x Y Hprime d sep blockA blockB hDisjoint
      m hm z.1.1 z.1.2 hν fA fB
      UA UB HC hU1 hU2 hH hHp hHupper
      M N M N hMp hNp (le_refl _) (le_refl _)
      hMA hNB theta k hk hOutside
  simpa only [UA,UB,HC] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueGlobalCellPairCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The EXACT number of attainable source03 SOURCE-B/TARGET-A
GLOBAL log-cell pairs, with actual ν-dependent prime supports
and original independent widths hB,hA, is bounded by the
PRODUCT of two explicit real cell-count factors. This is the
precise retained-major globalization loss; the discarded-cell
budget is separate and must NOT be multiplied by this count. -/
theorem source_original_true_global_cell_pair_real_count434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (L d hA hB : ℝ)
    (hL : 1 ≤ L) (hhA : 0 < hA) (hhB : 0 < hB)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    (((sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) hB).product
      (sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) hA)).card:ℝ) ≤
      (((Fintype.card ν.2:ℝ)*L^d)/hB+2) *
      (((Fintype.card ν.1:ℝ)*L^d)/hA+2) := by
  classical
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) hB
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) hA
  have hCB : (CB.card:ℝ) ≤
      ((Fintype.card ν.2:ℝ)*L^d)/hB+2 :=
    source_original_true_BIG_candidate_cell_real_bound434
      (fun z : ν.2 => P z.val.1) L d hB hL hhB
      (fun z p hp => hPrimeB z p hp)
  have hCA : (CA.card:ℝ) ≤
      ((Fintype.card ν.1:ℝ)*L^d)/hA+2 :=
    source_original_true_BIG_candidate_cell_real_bound434
      (fun z : ν.1 => P z.val.1) L d hA hL hhA
      (fun z p hp => hPrimeA z p hp)
  have hCBup : 0 ≤ ((Fintype.card ν.2:ℝ)*L^d)/hB+2 := by
    positivity
  have hProd : (CB.card:ℝ)*(CA.card:ℝ) ≤
      (((Fintype.card ν.2:ℝ)*L^d)/hB+2) *
      (((Fintype.card ν.1:ℝ)*L^d)/hA+2) :=
    mul_le_mul hCB hCA (Nat.cast_nonneg _) hCBup
  change (((CB ×ˢ CA).card:ℝ)) ≤ _
  rw [Finset.card_product]
  push_cast
  exact hProd
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCoarseDyadicUniformBudget -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Uniform bound for the TRUE attainable COARSE dyadic cell pairs.
The source group count is C0*log L and each group has at most tmax
freed probes. The threshold is chosen BEFORE the group type, pattern
and prime sets. No fixed total-probe cap and no fine-mesh parameter
occur. This is the counting cost available after dyadic alignment. -/
theorem eventually_source_original_coarse_dyad_pair_count434
    (C0 d : ℝ) (hC0 : 0 ≤ C0) (hd : 0 ≤ d) (tmax : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L)
      (m : ℕ) (hm : m ≤ tmax)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ)
      (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)),
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log 2)
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log 2)
    ((CB.product CA).card:ℝ) ≤ L^(2*d+4) := by
  let c : ℝ := (tmax:ℝ)*C0/Real.log 2
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) hlog.le
  filter_upwards [eventually_ge_atTop (max (1:ℝ) (c+2))] with L hLarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hLarge
  have hScale : c+2 ≤ L := (le_max_right _ _).trans hLarge
  have hLp : 0 < L := by linarith
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hLp]
  have hPow : 1 ≤ L^d := Real.one_le_rpow hL hd
  have hPow0 : 0 ≤ L^d := Real.rpow_nonneg hLp.le _
  intro G instF instD hGroups m hm ν P hPrimeA hPrimeB
  classical
  have hSlots (A : Finset (G × Fin m)) :
      (Fintype.card A:ℝ) ≤ (tmax:ℝ)*C0*Real.log L := by
    calc
      (Fintype.card A:ℝ) = (A.card:ℝ) := by simp
      _ ≤ (Fintype.card (G × Fin m):ℝ) := by
        exact_mod_cast Finset.card_le_univ A
      _ = (Fintype.card G:ℝ)*(m:ℝ) := by simp
      _ ≤ (C0*Real.log L)*(tmax:ℝ) :=
        mul_le_mul hGroups (by exact_mod_cast hm)
          (Nat.cast_nonneg _) (mul_nonneg hC0 hLogL)
      _ = (tmax:ℝ)*C0*Real.log L := by ring
  have hCommon : c*Real.log L*L^d+2 ≤ L^(d+2) := by
    have hcLog : c*Real.log L*L^d ≤ c*L*L^d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogL hc) hPow0
    have hLPow : 1 ≤ L*L^d := by nlinarith
    calc
      _ ≤ c*L*L^d + 2*L*L^d := by nlinarith
      _ = (c+2)*L*L^d := by ring
      _ ≤ L*L*L^d := by gcongr
      _ = L^(d+2) := by
        rw [Real.rpow_add hLp d 2,Real.rpow_two]
        ring
  have hSide (A : Finset (G × Fin m)) :
      ((Fintype.card A:ℝ)*L^d)/Real.log 2+2 ≤ L^(d+2) := by
    calc
      _ ≤ (((tmax:ℝ)*C0*Real.log L)*L^d)/Real.log 2+2 := by
        gcongr
        exact hSlots A
      _ = c*Real.log L*L^d+2 := by dsimp [c]; ring
      _ ≤ L^(d+2) := hCommon
  have hCount := source_original_true_global_cell_pair_real_count434
    m ν P L d (Real.log 2) (Real.log 2) hL hlog hlog hPrimeA hPrimeB
  dsimp only
  calc
    _ ≤ (((Fintype.card ν.2:ℝ)*L^d)/Real.log 2+2) *
          (((Fintype.card ν.1:ℝ)*L^d)/Real.log 2+2) := hCount
    _ ≤ L^(d+2)*L^(d+2) :=
      mul_le_mul (hSide ν.2) (hSide ν.1) (by positivity)
        (Real.rpow_nonneg hLp.le _)
    _ = L^(2*d+4) := by
      rw [← Real.rpow_add hLp]
      congr 1
      ring

/-- A concrete acyclic exponent choice for the verified minor estimate
and the coarse dyadic-pair count. Conductor and retention exponents
may be chosen AFTER D; they do not re-enter this minor budget. -/
theorem source_original_coarse_minor_budget_witness434
    (Bgoal d : ℝ) (hGoal : 0 ≤ Bgoal) (hd : 0 ≤ d) (C : ℕ) :
    let Bsave := Bgoal+2*d+5
    let D := Bsave+2*(C:ℝ)
    0 < Bsave ∧ 0 ≤ D ∧ Bsave+2*(C:ℝ) ≤ D ∧
      Bgoal+(2*d+4)+1 ≤ Bsave := by
  dsimp only
  have hC : (0:ℝ) ≤ C := Nat.cast_nonneg _
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAlignedMeshDiscardedBudget -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- An explicit mesh that exactly subdivides the TRUE dyads while
retaining polynomial inverse width. It is chosen before all labels. -/
theorem eventually_source_original_aligned_mesh_bounds434
    (H : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop,
    let N : ℕ := Nat.ceil (4*L^H)
    let h : ℝ := Real.log 2/(N:ℝ)
    0 < N ∧ 0 < h ∧ h+h ≤ L^(-H) ∧ h⁻¹ ≤ L^(H+1) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogUpper : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  filter_upwards [eventually_ge_atTop (max (1:ℝ) (5/Real.log 2))] with L hLarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hLarge
  have hLp : 0 < L := by linarith
  have hConst : 5/Real.log 2 ≤ L := (le_max_right _ _).trans hLarge
  have hP : 1 ≤ L^H := Real.one_le_rpow hL hH
  have hPpos : 0 < L^H := Real.rpow_pos_of_pos hLp _
  let N : ℕ := Nat.ceil (4*L^H)
  have hNlow : 4*L^H ≤ (N:ℝ) := Nat.le_ceil _
  have hNpos : 0 < (N:ℝ) := by linarith
  have hNat : 0 < N := by exact_mod_cast hNpos
  have hNup : (N:ℝ) ≤ 5*L^H := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*L^H)
    change (Nat.ceil (4*L^H):ℝ) ≤ 5*L^H
    linarith
  dsimp only
  refine ⟨hNat,div_pos hlog hNpos,?_,?_⟩
  · rw [Real.rpow_neg hLp.le,← one_div]
    apply (le_div_iff₀ hPpos).2
    have hRecip : Real.log 2/(N:ℝ)+Real.log 2/(N:ℝ) = 2*Real.log 2/(N:ℝ) := by ring
    rw [hRecip]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hNpos).2
    nlinarith
  · calc
      _ = (N:ℝ)/Real.log 2 := by simp [N]
      _ ≤ (5*L^H)/Real.log 2 := (div_le_div_iff_of_pos_right hlog).2 hNup
      _ = (5/Real.log 2)*L^H := by ring
      _ ≤ L*L^H := mul_le_mul_of_nonneg_right hConst hPpos.le
      _ = L^(H+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring

/-- Uniform payment for actual DISCARDED fine cells with the explicit
aligned mesh and xi=L^-Cxi. Counts enter once in a rare-event budget;
they are never used to sum the coherent retained minor kernel.
The eventual threshold precedes the growing group and probe data. -/
theorem eventually_source_original_aligned_discarded_budget434
    (C0 d H Cxi Bsave : ℝ)
    (hC0 : 0 ≤ C0) (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hSaving : Bsave+H+d+4 ≤ Cxi) (tmax : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L)
      (m : ℕ) (hm : m ≤ tmax)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ)
      (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)),
    let N : ℕ := Nat.ceil (4*L^H)
    let h : ℝ := Real.log 2/(N:ℝ)
    let nA := (sourceOriginalCandidateLogCells434 (fun z : ν.1 => P z.val.1) h).card
    let nB := (sourceOriginalCandidateLogCells434 (fun z : ν.2 => P z.val.1) h).card
    2*((nA+nB:ℕ):ℝ)*L^(-Cxi) ≤ L^(-Bsave) := by
  let c : ℝ := (tmax:ℝ)*C0
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) hC0
  filter_upwards [eventually_source_original_aligned_mesh_bounds434 H hH,
    eventually_ge_atTop (max (4:ℝ) (c+2))] with L hMesh hLarge
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hLarge
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hcL : c+2 ≤ L := (le_max_right _ _).trans hLarge
  have hLogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLp]
  let N : ℕ := Nat.ceil (4*L^H)
  let h : ℝ := Real.log 2/(N:ℝ)
  have hh : 0 < h := hMesh.2.1
  have hInv : h⁻¹ ≤ L^(H+1) := hMesh.2.2.2
  intro G instF instD hGroups m hm ν P hPrimeA hPrimeB
  classical
  have hSlots (A : Finset (G × Fin m)) :
      (Fintype.card A:ℝ) ≤ c*Real.log L := by
    calc
      (Fintype.card A:ℝ) = (A.card:ℝ) := by simp
      _ ≤ (Fintype.card (G × Fin m):ℝ) := by exact_mod_cast Finset.card_le_univ A
      _ = (Fintype.card G:ℝ)*(m:ℝ) := by simp
      _ ≤ (C0*Real.log L)*(tmax:ℝ) :=
        mul_le_mul hGroups (by exact_mod_cast hm)
          (Nat.cast_nonneg _) (mul_nonneg hC0 hLogL)
      _ = c*Real.log L := by dsimp [c]; ring
  have hSide (A : Finset (G × Fin m))
      (hPrime : ∀ z : A, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
      ((sourceOriginalCandidateLogCells434 (fun z : A => P z.val.1) h).card:ℝ) ≤
        L^(H+d+3) := by
    have hBase := source_original_true_BIG_candidate_cell_real_bound434
      (fun z : A => P z.val.1) L d h hL hh hPrime
    have hPow0 : 0 ≤ L^d := Real.rpow_nonneg hLp.le _
    have hPow1 : 1 ≤ L^(H+d+2) := Real.one_le_rpow hL (by linarith)
    have hPowerEq : L*L^d*L^(H+1) = L^(H+d+2) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      ring
    calc
      _ ≤ ((Fintype.card A:ℝ)*L^d)/h+2 := hBase
      _ = ((Fintype.card A:ℝ)*L^d)*h⁻¹+2 := by rw [div_eq_mul_inv]
      _ ≤ (c*Real.log L*L^d)*L^(H+1)+2 := by gcongr; exact hSlots A
      _ ≤ (c*L*L^d)*L^(H+1)+2 := by gcongr
      _ = c*L^(H+d+2)+2 := by rw [← hPowerEq]; ring
      _ ≤ (c+2)*L^(H+d+2) := by nlinarith
      _ ≤ L*L^(H+d+2) := by gcongr
      _ = L^(H+d+3) := by
        nth_rw 1 [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  have hA := hSide ν.1 hPrimeA
  have hB := hSide ν.2 hPrimeB
  dsimp only
  have hCount : (((sourceOriginalCandidateLogCells434 (fun z : ν.1 => P z.val.1) h).card+
      (sourceOriginalCandidateLogCells434 (fun z : ν.2 => P z.val.1) h).card:ℕ):ℝ) ≤
      2*L^(H+d+3) := by push_cast; linarith
  calc
    _ ≤ 4*L^(H+d+3)*L^(-Cxi) := by
      have hh := mul_le_mul_of_nonneg_right hCount (Real.rpow_nonneg hLp.le (-Cxi))
      nlinarith
    _ ≤ L*L^(H+d+3)*L^(-Cxi) := by gcongr
    _ = L^(H+d+4-Cxi) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      ring
    _ ≤ L^(-Bsave) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAlignedPhysicalChoices -/

section

open Filter Real
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Uniform original physical side conditions for the explicit
Q, aligned mesh and retention threshold. Constants precede all moving
prime labels and all integer Fourier modes in the fixed polynomial band.
The SW endpoint threshold is absorbed by the actual exponential lower
bound, and Q^2<=lo follows from exp(L^gamma)<=lo+1. -/
theorem eventually_source_original_ALIGNED_physical_choices434
    (Cq Cxi : ℕ) (D Ck H gamma gammaBig Y0 : ℝ)
    (hD : 0 ≤ D) (hCk : 0 ≤ Ck) (hH : 0 ≤ H)
    (hgamma : 0 < gamma) (hgammaBig : 0 < gammaBig)
    (hCq : D+Ck+2 ≤ (Cq:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ L^D ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ L^Cq ∧
    0<h ∧ h+h ≤ 1 ∧ 0<xi ∧ xi⁻¹ ≤ L^Cxi ∧
    ((Real.log (2:ℝ))⁻¹+1) ≤ L ∧
    (∀ u : ℕ, Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ) →
      1≤u ∧ Q^2≤u ∧ Y0 ≤ ((u+1:ℕ):ℝ)) ∧
    (∀ p : ℕ, Real.exp (L^gammaBig) ≤ (p:ℝ) → Q^2<p) ∧
    (∀ k : ℤ, (k.natAbs:ℝ) ≤ L^Ck →
      k.natAbs*Nat.ceil (L^(D+1)) ≤ Q) := by
  have hExp : ∀ᶠ L : ℝ in atTop,
      max (2:ℝ) Y0 ≤ Real.exp (L^gamma) :=
    (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hgamma)).eventually
      (eventually_ge_atTop (max (2:ℝ) Y0))
  filter_upwards [
    eventually_source_original_aligned_conductor_choice434 D Ck Cq hD hCk hCq,
    eventually_source_original_aligned_mesh_bounds434 H hH,
    eventually_source_original_conductor_below_BIG434 Cq gamma hgamma,
    eventually_source_original_conductor_below_BIG434 Cq gammaBig hgammaBig,
    hExp,eventually_ge_atTop (max (1:ℝ) ((Real.log (2:ℝ))⁻¹+1))]
    with L hQ hMesh hEndpoint hPrime hExpL hLarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hLarge
  have hLp : 0 < L := by linarith
  have hLd : ((Real.log (2:ℝ))⁻¹+1) ≤ L := (le_max_right _ _).trans hLarge
  let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  have hWidth : h+h ≤ 1 := hMesh.2.2.1.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith))
  have hxi : 0<xi := Real.rpow_pos_of_pos hLp _
  have hXi : xi⁻¹ ≤ L^Cxi := by
    dsimp [xi]
    rw [Real.rpow_neg hLp.le,inv_inv,Real.rpow_natCast]
  refine ⟨hQ.1,hQ.2.1,hQ.2.2.1,hMesh.2.1,hWidth,hxi,hXi,hLd,?_,?_,hQ.2.2.2⟩
  · intro u hu
    have hTwo : (2:ℝ) ≤ ((u+1:ℕ):ℝ) :=
      ((le_max_left (2:ℝ) Y0).trans hExpL).trans hu
    have huNat : 2 ≤ u+1 := by exact_mod_cast hTwo
    have hQu : Q^2 < u+1 := hEndpoint Q (u+1) hQ.2.2.1 hu
    refine ⟨by omega,Nat.lt_succ_iff.mp hQu,?_⟩
    exact ((le_max_right (2:ℝ) Y0).trans hExpL).trans hu
  · intro p hp
    exact hPrime Q p hQ.2.2.1 hp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMovingMajorUnion -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The EXACT finite union of the original source03
major arcs over ALL actual five-index ν/active-cell/
primitive-character modes. Critically Hcell(z) moves
with jA,jB and ν; no fictitious shared Hprime radius. -/
noncomputable def sourceOriginalTrueMovingMajorUnion434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Qchar : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi L D Carc : ℝ) (k : ℤ) : Set (AddCircle (1:ℝ)) :=
  ⋃ z ∈ sourceOriginalProbeExpandedFamily434
    blockA blockB m Qchar P V hA hB xi,
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/sourceOriginalProbeTrueHprime434
          m Qchar hA hB z)
/-- Being outside the union means being outside EACH
one of the TRUE moving original major arcs. This is
proved without changing the radius, conductor range,
sign of k, family, or source output cells. -/
theorem source_original_true_moving_major_union_outside434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Qchar : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi L D Carc : ℝ) (k : ℤ)
    (theta : AddCircle (1:ℝ))
    (hOutside : theta ∉ sourceOriginalTrueMovingMajorUnion434
      blockA blockB m Qchar P V hA hB xi L D Carc k)
    (z : Σ ν : SourceOriginalProbePattern434 G m,
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Qchar,DirichletCharacter ℂ (q.val+1))))
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar P V hA hB xi) :
    theta ∉ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^Carc/sourceOriginalProbeTrueHprime434
        m Qchar hA hB z) := by
  intro hMem
  apply hOutside
  exact Set.mem_iUnion₂.mpr ⟨z,hz,hMem⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMovingUnionFrequencyLift -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Inside the TRUE union of ORIGINAL ν-dependent five-index
moving rational arcs, select SOME genuine z and a rational
h/q with q <= |k| *ceil(L^(D+1)), and extract a real
integer-period lift for the actual Fourier frequency -k*theta.
The irrational remainder MUST cost |k| times the radius
L^Carc/Hcell(z). Other five-index modes need separate arc
tests; membership in the union cannot control them all. -/
theorem source_original_true_moving_union_frequency_real_lift434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Qchar : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi L D Carc : ℝ) (k : ℤ) (theta : ℝ)
    (hMajor : (theta : AddCircle (1:ℝ)) ∈
      sourceOriginalTrueMovingMajorUnion434
        blockA blockB m Qchar P V hA hB xi L D Carc k) :
    ∃ z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar P V hA hB xi,
      ∃ q : ℕ, 0 < q ∧ q ≤
        k.natAbs*Nat.ceil (L^(D+1)) ∧
      ∃ h : ℕ, h < q ∧
      ∃ n : ℤ, ∃ beta : ℝ,
        |beta| ≤ |(k:ℝ)| *
          (L^Carc/sourceOriginalProbeTrueHprime434
            m Qchar hA hB z) ∧
        -(k:ℝ)*theta =
          (((-(k*(h:ℤ))):ℤ):ℝ)/(q:ℝ)
            + beta - ((k*n:ℤ):ℝ) := by
  classical
  change (theta:AddCircle (1:ℝ)) ∈
      ⋃ z ∈ sourceOriginalProbeExpandedFamily434
        blockA blockB m Qchar P V hA hB xi,
        sourceCircleRationalArcs434
          (k.natAbs*Nat.ceil (L^(D+1)))
          (L^Carc/sourceOriginalProbeTrueHprime434
            m Qchar hA hB z) at hMajor
  obtain ⟨z,hz,hArc⟩ := Set.mem_iUnion₂.mp hMajor
  obtain ⟨q,hq,hqQ,h,hh,n,beta,hBeta,hPhase⟩ :=
    source_circle_rational_arc_frequency_real_lift434
      (k.natAbs*Nat.ceil (L^(D+1))) theta
      (L^Carc/sourceOriginalProbeTrueHprime434
        m Qchar hA hB z) k hArc
  exact ⟨z,hz,q,hq,hqQ,h,hh,n,beta,hBeta,hPhase⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuBigLongProducts -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- BOTH original SOURCE03 ν-selected comparison products
D_A,D_B consist of nonempty true BIG probe sets. If each
original supported BIG prime p satisfies the manuscript
lower interval bound p>=exp(L^cfg.cexp), EACH resulting
actual physical selected-mark product already exceeds that
same exponential. This is proved from actual ν index
NONEMPTINESS and true prime-mark coordinate supports, not
from the old formal independent F1,p1,F2,p2 placeholders.
The manuscript BIG support lower bound is explicit: the old
SourceComparisonData434 DOES NOT contain this premise. -/
theorem source_original_source03_true_nu_big_long_products434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hL : 0 ≤ L)
    (blockA blockB : Finset β)
    (m : ℕ) (A B : Finset (β × Fin m))
    (hPattern : (A,B) ∈
       sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
       Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (vA : SourceOriginalGramPrimeTuple434
       (fun z : A => d.Tb z.val.1))
    (vB : SourceOriginalGramPrimeTuple434
       (fun z : B => d.Tb z.val.1)) :
    Real.exp (L^cfg.cexp) ≤
      (sourceOriginalGramPrimeProduct434
        (fun z : A => d.Tb z.val.1) vA:ℝ) ∧
    Real.exp (L^cfg.cexp) ≤
      (sourceOriginalGramPrimeProduct434
        (fun z : B => d.Tb z.val.1) vB:ℝ) := by
  classical
  obtain ⟨hNonA,_,hNonB,_⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m A B).mp hPattern
  have hIndexA : Nonempty A := by
    obtain ⟨z,hz⟩ := hNonA
    exact ⟨⟨z,hz⟩⟩
  have hIndexB : Nonempty B := by
    obtain ⟨z,hz⟩ := hNonB
    exact ⟨⟨z,hz⟩⟩
  have hMinA (z : A) :
      Real.exp (L^cfg.cexp) ≤ ((vA z).val:ℝ) :=
    hTbLower z.val.1 (vA z).val (vA z).property
  have hMinB (z : B) :
      Real.exp (L^cfg.cexp) ≤ ((vB z).val:ℝ) :=
    hTbLower z.val.1 (vB z).val (vB z).property
  constructor
  · exact source_original_nonempty_selected_BIG_product_lower434
      hIndexA (fun z : A => (vA z).val) L cfg.cexp hL hMinA
  · exact source_original_nonempty_selected_BIG_product_lower434
      hIndexB (fun z : B => (vB z).val) L cfg.cexp hL hMinB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuC6EventuallyBoundaries -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The three exact C6 dyadic boundary scale requirements
are true for all sufficiently large L directly from the
ORIGINAL ν-pattern's ACTUAL nonempty A and B BIG prime
products: no reuse of the old unrelated F1,p1,F2,p2
fields. When true supported BIG primes have the manuscript
lower scale p>=exp(L^cexp) and both selected products lie
in their actual containing integer windows [M,M+P)⊆[M,2M]
and [N,N+Q)⊆[N,2N], any r<=L^cfg.Carc
satisfies N>=L^D, M>=L^D log(2r),
MN>=L^D r log(2r), uniformly in moving prime marks.
Only the manuscript BIG lower prime support remains a
transparent explicit source admissibility hypothesis,
because SourceComparisonData434 omitted it. -/
theorem source_original_source03_true_nu_eventual_C6_boundaries434
    (cfg : SourceComparisonFixed434) (D : ℝ)
    (hD : 0 ≤ D) :
    ∃ L0 : ℝ, ∀ L : ℝ, L0 ≤ L →
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (blockA blockB : Finset β)
      (m : ℕ) (A B : Finset (β × Fin m))
      (hPattern : (A,B) ∈
        sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
        Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (vA : SourceOriginalGramPrimeTuple434
        (fun z : A => d.Tb z.val.1))
      (vB : SourceOriginalGramPrimeTuple434
        (fun z : B => d.Tb z.val.1))
      (M N r : ℕ)
      (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
      (hrCap : (r:ℝ) ≤ L^cfg.Carc)
      (hDyadA :
        ((sourceOriginalGramPrimeProduct434
          (fun z : A => d.Tb z.val.1) vA:ℕ):ℝ) ≤ 2*(M:ℝ))
      (hDyadB :
        ((sourceOriginalGramPrimeProduct434
          (fun z : B => d.Tb z.val.1) vB:ℕ):ℝ) ≤ 2*(N:ℝ)),
      L^D ≤ (N:ℝ) ∧
      L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ) ∧
      L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
        (M:ℝ)*(N:ℝ) := by
  have hc : 0 < cfg.cexp := by
    linarith [cfg.haexp, cfg.hab, cfg.hbc]
  obtain ⟨L0,hLarge⟩ :=
    source_original_circle_eventual_exp_dominance434
      cfg.cexp D cfg.Carc hc hD cfg.hCarc
  refine ⟨L0,?_⟩
  intro L hL
  obtain ⟨hL4,hDom⟩ := hLarge L hL
  intro ι β instI instIE instB instBE
    x Y Hprime d blockA blockB m A B hPattern hTbLower
    vA vB M N r hM hN hr hrCap hDyadA hDyadB
  obtain ⟨hLongA,hLongB⟩ :=
    source_original_source03_true_nu_big_long_products434
      cfg x L Y Hprime d (by linarith)
      blockA blockB m A B hPattern hTbLower vA vB
  have hUpperA : Real.exp (L^cfg.cexp) ≤ 2*(M:ℝ) :=
    hLongA.trans hDyadA
  have hUpperB : Real.exp (L^cfg.cexp) ≤ 2*(N:ℝ) :=
    hLongB.trans hDyadB
  have hRNN : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
  have hSuper : 4*L^D*(r:ℝ)^2 ≤
      Real.exp (L^cfg.cexp) :=
    hDom (r:ℝ) hRNN hrCap
  have hMstrong : 2*L^D*(r:ℝ)^2 ≤ (M:ℝ) := by
    nlinarith [hSuper,hUpperA]
  have hRone : 1 ≤ (r:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr.ne')
  have hRsq : 1 ≤ (r:ℝ)^2 := by
    nlinarith [sq_nonneg ((r:ℝ)-1)]
  have hPow : 0 ≤ L^D :=
    Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _
  have hSuperN : 2*L^D ≤ 4*L^D*(r:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hRsq
      (by positivity : 0 ≤ 4*L^D)
    nlinarith
  have hNlarge : L^D ≤ (N:ℝ) := by
    nlinarith [hSuper,hSuperN,hUpperB]
  obtain ⟨hMlog,hMNlog⟩ :=
    source_original_C6_actual_boundary_log_scales434
      M N r L D hM hN hr (by linarith)
      hNlarge hMstrong
  exact ⟨hNlarge,hMlog,hMNlog⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuWeightedPrimitiveModeMinor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- One actual primitive source03 character/cell factor is
a complex contraction, for EVERY integer input product. -/
theorem source_original_true_primitive_input_cell_norm_le_one434
    (Q : ℕ) (h : ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (n : ℕ) :
    ‖sourceOriginalPrimitiveInputCellMode434 Q h j c n‖ ≤ 1 := by
  unfold sourceOriginalPrimitiveInputCellMode434
  split_ifs
  · rw [norm_star]
    exact c.2.norm_le_one _
  · simp

/-- SOURCE03 C6 physical Fourier minor for ONE genuine ν and
primitive A/B cell mode, with ARBITRARY COMPLEX marked tests
in weighted L², not just tests pointwise bounded by one.
The primitive input factors contract each original prime-tuple
energy. The square-saving is the genuine C6 arithmetic theorem
with original -k theta; no new analytic saving is assumed. -/
theorem source_original_true_nu_weighted_primitive_mode_minor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
       [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (ν : SourceOriginalProbePattern434 β m)
    (hPattern : ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (Qchar : ℕ)
    (cA cB : Σ q : Fin Qchar,
      DirichletCharacter ℂ (q.val+1))
    (hA hB : ℝ) (jA jB : ℤ)
    (bA : SourceOriginalGramPrimeTuple434
       (fun z : ν.1 => d.Tb z.val.1) → ℂ)
    (bB : SourceOriginalGramPrimeTuple434
       (fun z : ν.2 => d.Tb z.val.1) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
      (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => bA v *
        sourceOriginalPrimitiveInputCellMode434
          Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)
    let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => bB v *
        sourceOriginalPrimitiveInputCellMode434
          Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)
    let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA v*‖bA v‖^2
    let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB v*‖bB v‖^2
    let AW := (Finset.range P).image (fun i => M+i)
    let BW := (Finset.range Q).image (fun j => N+j)
    ‖(∑ vA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
        (∑ vB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA vA *
                   sourceOriginalGramPrimeProduct434 SB vB):ℕ):ℤ)
          else 0)
      else 0)‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => bA v * sourceOriginalPrimitiveInputCellMode434
      Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => bB v * sourceOriginalPrimitiveInputCellMode434
      Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)
  let EA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖bA v‖^2
  let EB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖bB v‖^2
  let EFA : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2
  let EFB : ℝ := ∑ v : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2
  let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
  let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
  have hVposA (z : ν.1) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hVposB (z : ν.2) : 0 < d.Vbig z.val.1 :=
    cfg.hv.trans_le (d.hVbig z.val.1)
  have hmuA (z : ν.1) (p : ℕ) (hp : p ∈ SA z) :
      0 ≤ muA z p := by
    have hPrime : p.Prime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by exact_mod_cast hPrime.pos
    dsimp [muA]
    exact div_nonneg (div_nonneg zero_le_one hpp.le)
      (hVposA z).le
  have hmuB (z : ν.2) (p : ℕ) (hp : p ∈ SB z) :
      0 ≤ muB z p := by
    have hPrime : p.Prime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < p := by exact_mod_cast hPrime.pos
    dsimp [muB]
    exact div_nonneg (div_nonneg zero_le_one hpp.le)
      (hVposB z).le
  have hmassA (v : SourceOriginalGramPrimeTuple434 SA) :
      0 ≤ sourceOriginalGramPrimeMass434 SA muA v :=
    source_original_physical_gram_prime_mass_nonneg434
      SA muA hmuA v
  have hmassB (v : SourceOriginalGramPrimeTuple434 SB) :
      0 ≤ sourceOriginalGramPrimeMass434 SB muB v :=
    source_original_physical_gram_prime_mass_nonneg434
      SB muB hmuB v
  have hfA (v : SourceOriginalGramPrimeTuple434 SA) :
      ‖fA v‖ ≤ ‖bA v‖ := by
    change ‖bA v *
      sourceOriginalPrimitiveInputCellMode434
        Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)‖ ≤ _
    rw [norm_mul]
    calc
      ‖bA v‖ * ‖sourceOriginalPrimitiveInputCellMode434
          Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v)‖ ≤
          ‖bA v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (source_original_true_primitive_input_cell_norm_le_one434
            Qchar hA jA cA (sourceOriginalGramPrimeProduct434 SA v))
          (norm_nonneg _)
      _ = ‖bA v‖ := mul_one _
  have hfB (v : SourceOriginalGramPrimeTuple434 SB) :
      ‖fB v‖ ≤ ‖bB v‖ := by
    change ‖bB v *
      sourceOriginalPrimitiveInputCellMode434
        Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)‖ ≤ _
    rw [norm_mul]
    calc
      ‖bB v‖ * ‖sourceOriginalPrimitiveInputCellMode434
          Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v)‖ ≤
          ‖bB v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (source_original_true_primitive_input_cell_norm_le_one434
            Qchar hB jB cB (sourceOriginalGramPrimeProduct434 SB v))
          (norm_nonneg _)
      _ = ‖bB v‖ := mul_one _
  have hEFA : EFA ≤ EA := by
    dsimp [EFA,EA]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hfA v) 2) (hmassA v)
  have hEFB : EFB ≤ EB := by
    dsimp [EFB,EB]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hfB v) 2) (hmassB v)
  have hEFA0 : 0 ≤ EFA := by
    dsimp [EFA]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (hmassA v) (sq_nonneg _)
  have hEFB0 : 0 ≤ EFB := by
    dsimp [EFB]
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (hmassB v) (sq_nonneg _)
  have hEA0 : 0 ≤ EA := hEFA0.trans hEFA
  have hEB0 : 0 ≤ EB := hEFB0.trans hEFB
  have hProd : EFA*EFB ≤ EA*EB := by
    calc
      EFA*EFB ≤ EA*EFB :=
        mul_le_mul_of_nonneg_right hEFA hEFB0
      _ ≤ EA*EB := mul_le_mul_of_nonneg_left hEFB hEA0
  have hBase :=
    source_original_source03_true_nu_two_big_physical_minor_L2_log_power434
      cfg x L Y Hprime d sep
      blockA blockB hDisjoint m hm ν.1 ν.2 hPattern
      fA fB M N P Q hM hN a r beta0 hr hcop hbeta
      hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge
      C hExponent hSaving
  have hPhase :=
    source_original_physical_minor_fourier_phase_identity434
      SA muA SB muB fA fB AW BW theta k a r beta0 hApprox
  dsimp only at hBase
  rw [hPhase] at hBase
  dsimp only
  have hSavingNN : 0 ≤ L^(-Bsave) :=
    Real.rpow_nonneg (by linarith : 0 ≤ L) _
  calc
    _ ≤ 125*(EFA*EFB)*L^(-Bsave) := by
      simpa only [SA,SB,muA,muB,EFA,EFB,AW,BW] using hBase
    _ = (EFA*EFB)*(125*L^(-Bsave)) := by ring
    _ ≤ (EA*EB)*(125*L^(-Bsave)) :=
      mul_le_mul_of_nonneg_right hProd
        (mul_nonneg (by norm_num) hSavingNN)
    _ = 125*(EA*EB)*L^(-Bsave) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSWPrefixTransfer -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact quantitative bridge from an ordinary RAW prime
Dirichlet-character interval sum, whose unconditional
source-exact Siegel–Walfisz theorem was independently
kernel-proved in direction D (Lean 4.32.0), to the
TRUE C37 original harmonic GLOBAL log-product-cell prefix.
No loss of BIG prefix length, duplicate prime mass,
moving-other-prime-product R, or fake centeredness. -/
theorem source_original_harmonic_cell_prefix_from_raw434
    (a n u v R : ℕ) (hR : 0 < R)
    (h : ℝ) (j : ℤ)
    (V : ℝ) (hV : 0 < V) (χ : ℕ → ℂ)
    (B : ℝ)
    (hRaw : ∀ k ∈ Finset.Icc a n,
      ‖∑ p ∈ Finset.Ioc
        (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
        (min k (min v (sourceOriginalLogCellExactUpper434 h j R))),
        if p.Prime then χ p else 0‖ ≤ B) :
    ∀ k ∈ Finset.Icc a n,
      ‖sourceOriginalPrimePrefix434 a k
       (sourceOriginalWeightedCellPrimeNumerator434
         (sourceOriginalActualPrimeBand434 u v)
         (fun p => (1/(p:ℝ))/V)
         (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
         χ)‖ ≤ B/V := by
  intro k hk
  rw [source_original_actual_harmonic_prefix_raw_eq434
    a k u v R hR h j V hV χ]
  rw [norm_mul]
  have hVnorm : ‖(V:ℂ)⁻¹‖ = V⁻¹ := by
    rw [norm_inv,Complex.norm_real]
    simp only [Real.norm_eq_abs,abs_of_pos hV]
  rw [hVnorm]
  calc
    _ ≤ V⁻¹ * B :=
      mul_le_mul_of_nonneg_left (hRaw k hk)
        (inv_nonneg.mpr hV.le)
    _ = B/V := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveSWLocal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Direct source03 ORIGINAL primitive-character global
cell bridge: after selecting true source BIG prime band
(u,v], literal probability µ_i(p)=1/(p V_g), and
original quotient character at common conductor ≤ Q²,
a classical RAW UNWEIGHTED PRIME INTERVAL bound B yields
the EXACT weighted primitive character Gram local bound
B/(V_g*(a+1)) by finite Abel, where a is the REAL moving
natural cutoff of the global log-product cell.
This is the precise interface to D's kernel-proved
unconditional SourcePrimeSiegelWalfisz, NOT a hypothetical
prebounded operator or an independent log-cell model. -/
theorem source_original_actual_primitive_local_from_raw_SW434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (hh : 0 < h) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (i : ι)
    (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})
    (u v : ℕ) (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (B : ℝ) (hB : 0 ≤ B)
    (hRaw : ∀ k ∈ Finset.Icc
      (sourceOriginalLogCellPrimeLower434 h j
        (sourceOriginalGramOtherPrimeProduct434 S i r))
      (sourceOriginalLogCellPrimeUpper434 h j
        (sourceOriginalGramOtherPrimeProduct434 S i r)),
      ‖∑ p ∈ Finset.Ioc
         (max
          (sourceOriginalLogCellPrimeLower434 h j
            (sourceOriginalGramOtherPrimeProduct434 S i r))
          (max u (sourceOriginalLogCellExactLower434 h j
            (sourceOriginalGramOtherPrimeProduct434 S i r))))
         (min k (min v (sourceOriginalLogCellExactUpper434 h j
            (sourceOriginalGramOtherPrimeProduct434 S i r)))),
         if p.Prime then
           sourceOriginalPrimitivePairQuotient434 Q c d
             (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
         else 0‖ ≤ B) :
    ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
      (fun n => c.2 (n:ZMod (c.1.val+1)))
      (fun n => d.2 (n:ZMod (d.1.val+1))) i r‖ ≤
      (B/V) /
       (((sourceOriginalLogCellPrimeLower434 h j
        (sourceOriginalGramOtherPrimeProduct434 S i r)+1:ℕ):ℝ)) := by
  let R := sourceOriginalGramOtherPrimeProduct434 S i r
  let a := sourceOriginalLogCellPrimeLower434 h j R
  let n := sourceOriginalLogCellPrimeUpper434 h j R
  have hR : 0 < R :=
    source_original_gram_other_prime_product_pos434
      S i (fun k p hp => (hBIG k p hp).1) r
  let χ : ℕ → ℂ := fun p =>
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
  have hraw' : ∀ k ∈ Finset.Icc a n,
      ‖∑ p ∈ Finset.Ioc
         (max a (max u (sourceOriginalLogCellExactLower434 h j R)))
         (min k (min v (sourceOriginalLogCellExactUpper434 h j R))),
         if p.Prime then χ p else 0‖ ≤ B := by
    simpa only [a,n,R,χ] using hRaw
  have hmuEq : mu i =
      (fun p : ℕ => (1/(p:ℝ))/V) := by
    funext p
    exact hWeight p
  have hPrefix : ∀ k ∈ Finset.Icc a n,
      ‖sourceOriginalPrimePrefix434 a k
         (sourceOriginalWeightedCellPrimeNumerator434 (S i)
           (mu i)
           (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
           χ)‖ ≤ B/V := by
    intro k hk
    have hb := source_original_harmonic_cell_prefix_from_raw434
      a n u v R hR h j V hV χ B hraw' k hk
    simpa only [hBand,hmuEq] using hb
  exact source_original_primitive_gram_actual_cutoff_abel434
    S mu h hh j Q c d i hBIG r
      (B/V) (div_nonneg hB hV.le) hPrefix
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDyadicPrimitiveGramSharp -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Sharp source03 local Gram decay: the correct finite Abel anchor is
u, the actual lower BIG prime endpoint, NOT the sometimes much smaller
GLOBAL log-cell lower cutoff a. This cancels the SW factor u+1 exactly.
The only remaining premise is D's pointwise SW at y=u+1. -/
theorem source_original_dyadic_primitive_gram_sharp434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (hh : 0 < h) (j : ℤ) (Q Cq : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (r : (k : {k : ι // k ≠ i}) → {p : ℕ // p ∈ S k.val})
    (u v : ℕ) (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u) (huv : u ≤ v)
    (hdyad : v ≤ 2*(u+1))
    (hSW :
      ∀ (f aa bb : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f),
        χ.IsPrimitive → χ ≠ 1 →
        (f:ℝ) ≤ (Real.log ((u+1:ℕ):ℝ))^C →
        ((u+1:ℕ):ℝ) ≤ (aa:ℝ)+1 → aa ≤ bb →
        (bb:ℝ) ≤ 2*((u+1:ℕ):ℝ) →
        ‖∑ p ∈ Finset.Ioc aa bb, if p.Prime then χ p else 0‖ ≤
          K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)) :
    ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
      (fun p => c.2 (p:ZMod (c.1.val+1)))
      (fun p => d.2 (p:ZMod (d.1.val+1))) i r‖ ≤
    ((K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A))/V) /
      (((u+1:ℕ):ℝ)) := by
  let R := sourceOriginalGramOtherPrimeProduct434 S i r
  let lo := sourceOriginalLogCellExactLower434 h j R
  let hi := sourceOriginalLogCellExactUpper434 h j R
  let B : ℝ :=
    K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)
  have hy1 : (1:ℝ) ≤ ((u+1:ℕ):ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le u))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg hK (by positivity))
      (Real.rpow_nonneg (Real.log_nonneg hy1) _)
  have hRaw : ∀ k ∈ Finset.Icc u v,
      ‖∑ p ∈ Finset.Ioc (max u (max u lo))
        (min k (min v hi)),
        if p.Prime then
           sourceOriginalPrimitivePairQuotient434 Q c d
             (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
        else 0‖ ≤ B := by
    intro k hk
    let lower := max u (max u lo)
    let upper := min k (min v hi)
    have hbig : ∀ p ∈ Finset.Ioc lower upper,
        p.Prime → Q^2 < p := by
      intro p hp hpPrime
      have hpl := (Finset.mem_Ioc.mp hp).1
      dsimp [lower] at hpl
      omega
    have hpair :
        (∑ p ∈ Finset.Ioc lower upper,
          if p.Prime then sourceOriginalPrimitivePairQuotient434
            Q c d (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
          else 0) =
        (∑ p ∈ Finset.Ioc lower upper,
          if p.Prime then
            star (c.2 (p:ZMod (c.1.val+1))) *
              d.2 (p:ZMod (d.1.val+1)) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpPrime : p.Prime
      · simp only [if_pos hpPrime]
        exact (source_original_primitive_pair_prime_eval434
          Q c d p hpPrime (hbig p hp hpPrime)).symm
      · simp only [if_neg hpPrime]
    rw [hpair]
    exact source_original_moving_dyadic_SW_apply434
      Q Cq u v u k lo hi L gamma C A K hK hL hgamma hC
      hExponent hQ huLarge huBIG hdyad c d hc hd hne hSW
  have hR : 0 < R :=
    source_original_gram_other_prime_product_pos434
      S i (fun k p hp => (hBIG k p hp).1) r
  let chi : ℕ → ℂ := fun p =>
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
  have hmu : mu i = (fun p : ℕ => (1/(p:ℝ))/V) := by
    funext p
    exact hWeight p
  have hcover : ∀ p ∈ S i,
      sourceOriginalLiteralLogCell434 h j (p*R) →
      p ∈ Finset.Ioc u v := by
    intro p hp _
    rw [hBand] at hp
    exact (Finset.mem_filter.mp hp).1
  have hPrefix : ∀ k ∈ Finset.Icc u v,
      ‖sourceOriginalPrimePrefix434 u k
        (sourceOriginalWeightedCellPrimeNumerator434 (S i)
          (mu i) (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
          chi)‖ ≤ B/V := by
    intro k hk
    have hp := source_original_harmonic_cell_prefix_from_raw434
      u v u v R hR h j V hV chi B hRaw k hk
    simpa only [hBand,hmu,chi] using hp
  exact source_original_primitive_gram_local_from_prefix434
    S mu h j Q c d i (hBIG i) r u v huv
      hcover (B/V) (div_nonneg hB hV.le) hPrefix
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDyadicPrimitiveCellPiece -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original one-dyad physical harmonic character sum in a GLOBAL
log-product cell. Exact band, reciprocal prime law, R and V_g.
Unlike a surrogate arbitrary weighted operator, the only input
is the pointwise D-style Siegel–Walfisz estimate for primes. -/
theorem source_original_dyadic_primitive_cell_piece434
    (Q Cq u v R : ℕ) (hR : 0 < R)
    (h : ℝ) (j : ℤ) (V : ℝ) (hV : 0 < V)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u) (huv : u ≤ v)
    (hdyad : v ≤ 2*(u+1))
    (hSW :
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log ((u+1:ℕ):ℝ))^C →
        ((u+1:ℕ):ℝ) ≤ (aa:ℝ)+1 → aa ≤ bb →
        (bb:ℝ) ≤ 2*((u+1:ℕ):ℝ) →
        ‖∑ p ∈ Finset.Ioc aa bb, if p.Prime then chi p else 0‖ ≤
          K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)) :
    ‖∑ p ∈ sourceOriginalActualPrimeBand434 u v,
       (((1/(p:ℝ))/V):ℂ) *
         (if sourceOriginalLiteralLogCell434 h j (p*R) then
           sourceOriginalPrimitivePairQuotient434 Q c d
             (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
          else 0)‖ ≤
    ((K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A))/V) /
      (((u+1:ℕ):ℝ)) := by
  let lo := sourceOriginalLogCellExactLower434 h j R
  let hi := sourceOriginalLogCellExactUpper434 h j R
  let chi : ℕ → ℂ := fun p =>
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
  let B : ℝ :=
    K*((u+1:ℕ):ℝ)*(Real.log ((u+1:ℕ):ℝ))^(-A)
  have hy1 : (1:ℝ) ≤ ((u+1:ℕ):ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le u))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg hK (by positivity))
      (Real.rpow_nonneg (Real.log_nonneg hy1) _)
  have hRaw : ∀ k ∈ Finset.Icc u v,
      ‖∑ p ∈ Finset.Ioc (max u (max u lo))
        (min k (min v hi)),
        if p.Prime then chi p else 0‖ ≤ B := by
    intro k hk
    let lower := max u (max u lo)
    let upper := min k (min v hi)
    have hbig : ∀ p ∈ Finset.Ioc lower upper,
        p.Prime → Q^2 < p := by
      intro p hp hpPrime
      have hpl := (Finset.mem_Ioc.mp hp).1
      dsimp [lower] at hpl
      omega
    have hpair :
        (∑ p ∈ Finset.Ioc lower upper,
          if p.Prime then chi p else 0) =
        (∑ p ∈ Finset.Ioc lower upper,
          if p.Prime then
            star (c.2 (p:ZMod (c.1.val+1))) *
              d.2 (p:ZMod (d.1.val+1)) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpPrime : p.Prime
      · simp only [if_pos hpPrime]
        exact (source_original_primitive_pair_prime_eval434
          Q c d p hpPrime (hbig p hp hpPrime)).symm
      · simp only [if_neg hpPrime]
    rw [hpair]
    exact source_original_moving_dyadic_SW_apply434
      Q Cq u v u k lo hi L gamma C A K hK hL hgamma hC
      hExponent hQ huLarge huBIG hdyad c d hc hd hne hSW
  have hPrefix : ∀ k ∈ Finset.Icc u v,
      ‖sourceOriginalPrimePrefix434 u k
        (sourceOriginalWeightedCellPrimeNumerator434
          (sourceOriginalActualPrimeBand434 u v)
          (fun p => (1/(p:ℝ))/V)
          (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
          chi)‖ ≤ B/V := by
    intro k hk
    have hp := source_original_harmonic_cell_prefix_from_raw434
      u v u v R hR h j V hV chi B
      (by simpa only [lo,hi,chi] using hRaw) k hk
    exact hp
  have hpos : ∀ p ∈ sourceOriginalActualPrimeBand434 u v,
      0 < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.pos
  have hcover : ∀ p ∈ sourceOriginalActualPrimeBand434 u v,
      sourceOriginalLiteralLogCell434 h j (p*R) →
      p ∈ Finset.Ioc u v := by
    intro p hp _
    exact (Finset.mem_filter.mp hp).1
  simpa only [chi, B, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast] using
    (source_original_weighted_global_cell_prime_abel434
      (sourceOriginalActualPrimeBand434 u v)
      (fun p => (1/(p:ℝ))/V)
      (fun p => sourceOriginalLiteralLogCell434 h j (p*R))
      chi u v huv hpos hcover
      (B/V) (div_nonneg hB hV.le) hPrefix)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCompleteDyadicCell -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The TRUE source03 primitive-pair harmonic sum across ALL clipped
dyadic BIG subbands. No support, GLOBAL logarithmic cutoff, prime,
R, or V_g is replaced. SW is required only in the exact uniform
pointwise form furnished by D for all large real y. -/
theorem source_original_complete_dyadic_cell_bound434
    (Q Cq u v n R : ℕ)
    (huv : u ≤ v) (hcover : v ≤ u*2^n) (hR : 0 < R)
    (h : ℝ) (j : ℤ) (V : ℝ) (hV : 0 < V)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u)
    (hSW : ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb → (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤ K*y*(Real.log y)^(-A)) :
    ‖∑ p ∈ sourceOriginalActualPrimeBand434 u v,
       (((1/(p:ℝ))/V):ℂ) *
         (if sourceOriginalLiteralLogCell434 h j (p*R) then
           sourceOriginalPrimitivePairQuotient434 Q c d
             (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
          else 0)‖ ≤
    ∑ i ∈ Finset.range n,
      ((K*((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) := by
  let cell : ℕ → Prop :=
    fun p => sourceOriginalLiteralLogCell434 h j (p*R)
  let chi : ℕ → ℂ := fun p =>
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
  have hmon := sourceSWClippedDyad_mono434 u v
  have hstart : sourceSWClippedDyad434 u v 0 = u := by
    simp [sourceSWClippedDyad434, min_eq_right huv]
  have hbase (i : ℕ) : u ≤ sourceSWClippedDyad434 u v i := by
    simpa only [hstart] using hmon (Nat.zero_le i)
  have hcell :
      (∑ p ∈ sourceOriginalActualPrimeBand434 u v,
         (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0)) =
      ∑ i ∈ Finset.range n,
        ∑ p ∈ sourceOriginalActualPrimeBand434
          (sourceSWClippedDyad434 u v i)
          (sourceSWClippedDyad434 u v (i+1)),
          (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0) :=
    by
      simpa only [Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast] using
        (source_original_dyadic_harmonic_partition434
          u v n huv hcover (fun p => (1/(p:ℝ))/V) cell chi)
  have hpiece (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖∑ p ∈ sourceOriginalActualPrimeBand434
        (sourceSWClippedDyad434 u v i)
        (sourceSWClippedDyad434 u v (i+1)),
        (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0)‖ ≤
      ((K*((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) := by
    let x : ℕ := sourceSWClippedDyad434 u v i
    let z : ℕ := sourceSWClippedDyad434 u v (i+1)
    have hux : u ≤ x := hbase i
    have hxz : x ≤ z := hmon (Nat.le_succ i)
    have hxBIG : Q^2 ≤ x := huBIG.trans hux
    have hxLarge : Real.exp (L^gamma) ≤ ((x+1:ℕ):ℝ) := by
      apply huLarge.trans
      exact_mod_cast Nat.add_le_add_right hux 1
    have hxdyad : z ≤ 2*(x+1) :=
      source_original_clipped_dyadic_SW_width434 u v i
    have hyscale : ((u+1:ℕ):ℝ) ≤ ((x+1:ℕ):ℝ) := by
      exact_mod_cast Nat.add_le_add_right hux 1
    have hpoint := hSW ((x+1:ℕ):ℝ) hyscale
    have hb := source_original_dyadic_primitive_cell_piece434
      Q Cq x z R hR h j V hV c d hc hd hne
      L gamma C A K hK hL hgamma hC hExponent
      hQ hxLarge hxBIG hxz hxdyad hpoint
    simpa only [x,z,cell,chi] using hb
  change ‖∑ p ∈ sourceOriginalActualPrimeBand434 u v,
     (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0)‖ ≤ _
  calc
    _ = ‖∑ i ∈ Finset.range n,
      ∑ p ∈ sourceOriginalActualPrimeBand434
        (sourceSWClippedDyad434 u v i)
        (sourceSWClippedDyad434 u v (i+1)),
         (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0)‖ := by rw [hcell]
    _ ≤ ∑ i ∈ Finset.range n,
      ‖∑ p ∈ sourceOriginalActualPrimeBand434
         (sourceSWClippedDyad434 u v i)
         (sourceSWClippedDyad434 u v (i+1)),
          (((1/(p:ℝ))/V):ℂ) * (if cell p then chi p else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,
      ((K*((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) :=
      Finset.sum_le_sum (fun i hi => hpiece i hi)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullDyadicGramOffdiag -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Actual source03 offdiagonal GLOBAL-cell Gram on an ARBITRARY
long BIG prime band. All clipped dyads, moving other-prime product
R, physical harmonic law and both original character levels
remain exact. No loss by counting other-prime configurations. -/
theorem source_original_full_dyadic_primitive_gram_offdiag434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q Cq : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (u v n : ℕ) (huv : u ≤ v) (hcover : v ≤ u*2^n)
    (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u)
    (hSW : ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb → (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤ K*y*(Real.log y)^(-A)) :
    ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d‖ ≤
    ∑ t ∈ Finset.range n,
      ((K*((sourceSWClippedDyad434 u v t+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v t+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v t+1:ℕ):ℝ) := by
  let E : ℝ := ∑ t ∈ Finset.range n,
    ((K*((sourceSWClippedDyad434 u v t+1:ℕ):ℝ) *
      (Real.log ((sourceSWClippedDyad434 u v t+1:ℕ):ℝ))^(-A))/V) /
      ((sourceSWClippedDyad434 u v t+1:ℕ):ℝ)
  have hE : 0 ≤ E := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro t ht
    let x := sourceSWClippedDyad434 u v t
    have hy1 : (1:ℝ) ≤ ((x+1:ℕ):ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le x))
    have hypos : (0:ℝ) ≤ ((x+1:ℕ):ℝ) := by positivity
    have hpow :
        0 ≤ (Real.log ((x+1:ℕ):ℝ))^(-A) :=
      Real.rpow_nonneg (Real.log_nonneg hy1) _
    change 0 ≤ ((K*((x+1:ℕ):ℝ) *
        (Real.log ((x+1:ℕ):ℝ))^(-A))/V) /
        ((x+1:ℕ):ℝ)
    exact div_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg hK hypos) hpow) hV.le) hypos
  have hlocal (r : (k : {k : ι // k ≠ i}) →
      {p : ℕ // p ∈ S k.val}) :
    ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
      (fun p => c.2 (p:ZMod (c.1.val+1)))
      (fun p => d.2 (p:ZMod (d.1.val+1))) i r‖ ≤ E := by
    let R := sourceOriginalGramOtherPrimeProduct434 S i r
    let chi : ℕ → ℂ := fun p =>
      sourceOriginalPrimitivePairQuotient434 Q c d
        (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
    let cell : ℕ → Prop :=
      fun p => sourceOriginalLiteralLogCell434 h j (p*R)
    have hattach :
      (∑ p : {p : ℕ // p ∈ S i},
        (mu i p.val:ℂ) *
          (if cell p.val then chi p.val else 0)) =
      ∑ p ∈ S i,
        (mu i p:ℂ) * (if cell p then chi p else 0) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (S i)
          (fun p : ℕ => (mu i p:ℂ) *
            (if cell p then chi p else 0)))
    have hslice :=
      source_original_primitive_gram_local_quotient_slice434
        S mu h j Q c d i (hBIG i) r
    have hEq :
      sourceOriginalGramLocalPrimeSlice434 S mu h j
        (fun p => c.2 (p:ZMod (c.1.val+1)))
        (fun p => d.2 (p:ZMod (d.1.val+1))) i r =
      ∑ p ∈ sourceOriginalActualPrimeBand434 u v,
        (((1/(p:ℝ))/V):ℂ) *
          (if cell p then chi p else 0) := by
      rw [hslice, hattach, hBand]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hWeight p]
      simp only [Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_natCast]
    have hR : 0 < R :=
      source_original_gram_other_prime_product_pos434
        S i (fun k p hp => (hBIG k p hp).1) r
    rw [hEq]
    have hdyad := source_original_complete_dyadic_cell_bound434
      Q Cq u v n R huv hcover hR h j V hV c d hc hd hne
      L gamma C A K hK hL hgamma hC hExponent
      hQ huLarge huBIG hSW
    simpa only [E,cell,chi] using hdyad
  exact source_original_actual_primitive_gram_offdiag_from_one_prime434
    S mu hmu hmuPos h j Q c d hc hd i E hE hlocal
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDyadicLogSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The total loss from exact clipped dyadic decomposition is
at most the NUMBER n of dyads: on real scales y_i ≥ u+1,
every nonprincipal prime-character saving (log y_i)^(-A)
is at most (log(u+1))^(-A) for A>0. No product-label or
GLOBAL-cell counting factor is hidden in this inequality. -/
theorem source_original_clipped_dyadic_log_saving434
    (u v n : ℕ) (huv : u ≤ v)
    (K V A : ℝ) (hK : 0 ≤ K) (hV : 0 < V)
    (hA : 0 < A)
    (hlog : 0 < Real.log ((u+1:ℕ):ℝ)) :
    (∑ i ∈ Finset.range n,
      ((K*((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ)) ≤
    (n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A)) := by
  have hmon := sourceSWClippedDyad_mono434 u v
  have hstart : sourceSWClippedDyad434 u v 0 = u := by
    simp [sourceSWClippedDyad434, min_eq_right huv]
  have hbase (i : ℕ) : u ≤ sourceSWClippedDyad434 u v i := by
    simpa only [hstart] using hmon (Nat.zero_le i)
  have hsingle (i : ℕ) :
      ((K*((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) *
        (Real.log ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ))^(-A))/V) /
        ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ) ≤
      (K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A) := by
    let y : ℝ := ((sourceSWClippedDyad434 u v i+1:ℕ):ℝ)
    have hypos : 0 < y := by dsimp [y]; positivity
    have hy : ((u+1:ℕ):ℝ) ≤ y := by
      dsimp [y]
      exact_mod_cast Nat.add_le_add_right (hbase i) 1
    have hlogle : Real.log ((u+1:ℕ):ℝ) ≤ Real.log y :=
      Real.log_le_log (by positivity) hy
    have hpow :
        (Real.log y)^(-A) ≤
          (Real.log ((u+1:ℕ):ℝ))^(-A) :=
      Real.rpow_le_rpow_of_nonpos hlog hlogle (by linarith)
    change ((K*y*(Real.log y)^(-A))/V)/y ≤ _
    calc
      _ = (K/V) * (Real.log y)^(-A) := by
        field_simp [ne_of_gt hV, ne_of_gt hypos]
      _ ≤ (K/V) * (Real.log ((u+1:ℕ):ℝ))^(-A) :=
        mul_le_mul_of_nonneg_left hpow (div_nonneg hK hV.le)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A) :=
      Finset.sum_le_sum (fun i hi => hsingle i)
    _ = (n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A)) := by
      simp [mul_comm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullDyadicGramLogSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Physical source03 full GLOBAL cell Gram saving after all actual
clipped dyads: exactly the number n of dyads, with no
other-prime-tuple loss and no fake Gram orthogonality premise. -/
theorem source_original_full_dyadic_primitive_gram_log_saving434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q Cq : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (u v n : ℕ) (huv : u ≤ v) (hcover : v ≤ u*2^n)
    (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u)
    (hSW : ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb → (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤ K*y*(Real.log y)^(-A))
    (hA : 0 < A)
    (hlog : 0 < Real.log ((u+1:ℕ):ℝ)) :
    ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d‖ ≤
      (n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A)) := by
  have hdyad := source_original_full_dyadic_primitive_gram_offdiag434
    S mu hmu hmuPos h j Q Cq c d hc hd hne i hBIG
    u v n huv hcover V hV hBand hWeight
    L gamma C A K hK hL hgamma hC hExponent hQ huLarge huBIG hSW
  exact hdyad.trans
    (source_original_clipped_dyadic_log_saving434
      u v n huv K V A hK hV hA hlog)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalGramFractionalSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exact source03 physical off-diagonal Gram savings on a true
long BIG group, with the complete literal GLOBAL cell and moving
other-prime product, conditional ONLY on the source prime-character
SW pointwise bound and explicit source parameter growth.
This consumes the dyadic length n with no tuple or cell count loss. -/
theorem source_original_physical_gram_fractional_log_saving434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q Cq : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d)
    (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (u v n : ℕ) (huv : u ≤ v) (hcover : v ≤ u*2^n)
    (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (L gamma dExp C A B K : ℝ)
    (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hA : 0 < A)
    (hConductorExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u)
    (hdyadCount : (n:ℝ) ≤ L^dExp)
    (hSavingExponent : dExp+B ≤ gamma*A)
    (hlog : 0 < Real.log ((u+1:ℕ):ℝ))
    (hSW : ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb → (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤ K*y*(Real.log y)^(-A)) :
    ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d‖ ≤
      (K/V)*L^(-B) := by
  have hGram :=
    source_original_full_dyadic_primitive_gram_log_saving434
      S mu hmu hmuPos h j Q Cq c d hc hd hne i hBIG
      u v n huv hcover V hV hBand hWeight
      L gamma C A K hK hL hgamma hC hConductorExponent
      hQ huLarge huBIG hSW hA hlog
  exact hGram.trans
    (source_original_fractional_dyadic_log_absorb434
      n u L gamma dExp A B K V hL hgamma hA hK hV
      hdyadCount huLarge hSavingExponent)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualBigUnconditionalGram -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Arbitrary prescribed logarithmic saving for an ORIGINAL
source03 GLOBAL product-log cell. The dyadic count n is NOT
free: it is the source BIG-band count ceil(L^d/log 2).
The prime-character Siegel–Walfisz hypothesis is discharged
by the independently verified D proof, all inside Lean 4.34.1.
No matched-test SW or hypothetical Gram premise is used. -/
theorem source_original_actual_big_gram_power_unconditional434
    (Cq : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ)
      (c dchar : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)),
      c ∈ sourceOriginalActualPrimitiveCharacters434 Q →
      dchar ∈ sourceOriginalActualPrimitiveCharacters434 Q →
      c ≠ dchar →
      (i : ι) →
      (∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p) →
      (L : ℝ) → 1 ≤ L →
      ((Real.log (2:ℝ))⁻¹+1) ≤ L →
      (Q:ℝ) ≤ L^Cq →
      (u v : ℕ) → 1 ≤ u → u ≤ v →
      (v:ℝ) ≤ Real.exp (L^d) →
      Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ) →
      Q^2 ≤ u →
      Y ≤ ((u+1:ℕ):ℝ) →
      (V : ℝ) → 0 < V →
      S i = sourceOriginalActualPrimeBand434 u v →
      (∀ p, mu i p = (1/(p:ℝ))/V) →
      ‖sourceOriginalActualPrimitiveGramEntry434
        S mu h j Q c dchar‖ ≤
        (K/V)*L^(-B) := by
  let C : ℝ := (2*(Cq:ℝ)+1)/gamma
  let A : ℝ := (d+1+B)/gamma
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (by positivity) hgamma
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by linarith) hgamma
  have hConductor : 2*(Cq:ℝ) ≤ gamma*C := by
    dsimp [C]
    have hg : gamma ≠ 0 := ne_of_gt hgamma
    field_simp [hg]
    nlinarith
  have hSaving : (d+1)+B ≤ gamma*A := by
    dsimp [A]
    have hg : gamma ≠ 0 := ne_of_gt hgamma
    field_simp [hg]
    norm_num
  obtain ⟨K,hK,hSW⟩ :=
    Green64Analytic.SourceSW.sourcePrimeSiegelWalfisz_exact_body
      C A hC hA
  obtain ⟨Y,hEventually⟩ := Filter.eventually_atTop.1 hSW
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q c dchar
    hc hdchar hne i hBIG L hL hLdyad hQ
    u v hu huv hv huLarge huBIG hY V hV hBand hWeight
  let n := sourceOriginalSWDyadicCount434 L d
  have hcover : v ≤ u*2^n :=
    source_original_actual_SW_dyadic_count_cover434
      L d hL u v hu hv
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := hLpos.le
  have hcount : (n:ℝ) ≤ L^(d+1) := by
    have hdyad := source_original_actual_SW_dyadic_count_power434
      L d hL hd
    calc
      (n:ℝ) ≤ ((Real.log 2)⁻¹+1)*L^d := hdyad
      _ = L^d*((Real.log 2)⁻¹+1) := by ring
      _ ≤ L^d*L :=
        mul_le_mul_of_nonneg_left hLdyad
          (Real.rpow_nonneg hLnonneg _)
      _ = L^(d+1) := by
        rw [Real.rpow_add hLpos]
        simp
  have hLgamma : 0 < L^gamma :=
    Real.rpow_pos_of_pos hLpos _
  have hlog : 0 < Real.log ((u+1:ℕ):ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr hLgamma).trans_le huLarge)
  have hRealSW :
      ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb →
        (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤
            K*y*(Real.log y)^(-A) := by
    intro y hy f aa bb inst chi hp hn hf ha hab hb
    exact hEventually y (hY.trans hy) f aa bb chi
      hp hn hf ha hab hb
  exact source_original_physical_gram_fractional_log_saving434
    S mu hmu hmuPos h j Q Cq c dchar hc hdchar hne i hBIG
    u v n huv hcover V hV hBand hWeight
    L gamma (d+1) C A B K hK hL hgamma hC hA
    hConductor hQ huLarge huBIG hcount hSaving hlog hRealSW
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalGramSchur -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Actual finite family of the ORIGINAL source primitive
characters (all genuine levels q ≤ Q, with no replacement frame). -/
abbrev sourceOriginalPrimitiveFamily434 (Q : ℕ) :=
  {c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1) //
    c ∈ sourceOriginalActualPrimitiveCharacters434 Q}

/-- Source03 actual one-GLOBAL-cell near-frame operator in L²,
for arbitrary character coefficients; the SW input is only the
genuine prime-character theorem, not SW on an arbitrary H(p). -/
theorem source_original_actual_cell_near_gram_frame434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
    (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
    (h : ℝ) (j : ℤ) (Q Cq : ℕ)
    (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (u v n : ℕ) (huv : u ≤ v) (hcover : v ≤ u*2^n)
    (V : ℝ) (hV : 0 < V)
    (hBand : S i = sourceOriginalActualPrimeBand434 u v)
    (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
    (L gamma C A K : ℝ) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hgamma : 0 < gamma) (hC : 0 < C)
    (hExponent : 2*(Cq:ℝ) ≤ gamma*C)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
    (huBIG : Q^2 ≤ u)
    (hSW : ∀ y : ℝ, ((u+1:ℕ):ℝ) ≤ y →
      ∀ (f aa bb : ℕ) [NeZero f] (chi : DirichletCharacter ℂ f),
        chi.IsPrimitive → chi ≠ 1 →
        (f:ℝ) ≤ (Real.log y)^C →
        y ≤ (aa:ℝ)+1 → aa ≤ bb → (bb:ℝ) ≤ 2*y →
        ‖∑ p ∈ Finset.Ioc aa bb,
          if p.Prime then chi p else 0‖ ≤ K*y*(Real.log y)^(-A))
    (hA : 0 < A) (hlog : 0 < Real.log ((u+1:ℕ):ℝ))
    (a : sourceOriginalPrimitiveFamily434 Q → ℂ) :
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
      ‖∑ d : sourceOriginalPrimitiveFamily434 Q,
        sourceOriginalActualPrimitiveGramEntry434
          S mu h j Q c.val d.val * a d‖^2) ≤
    (1+(Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)*
      ((n:ℝ)*((K/V)*(Real.log ((u+1:ℕ):ℝ))^(-A))))^2 *
      (∑ d : sourceOriginalPrimitiveFamily434 Q, ‖a d‖^2) := by
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let G : Fam → Fam → ℂ := fun c d =>
    sourceOriginalActualPrimitiveGramEntry434
      S mu h j Q c.val d.val
  let eps : ℝ := (n:ℝ)*((K/V)*
    (Real.log ((u+1:ℕ):ℝ))^(-A))
  have heps : 0 ≤ eps := by
    dsimp [eps]
    have hpow : 0 ≤ (Real.log ((u+1:ℕ):ℝ))^(-A) :=
      Real.rpow_nonneg hlog.le _
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg hK hV.le) hpow)
  have hcell : sourceOriginalRealGramCellMass434
      S mu h j ≤ 1 :=
    (source_original_real_gram_cell_probability434
      S mu hmu hmuPos h j).2
  have hdiag (c : Fam) : ‖G c c‖ ≤ 1 := by
    exact (source_original_actual_primitive_gram_norm_le_mass434
       S mu hmuPos h j Q hBIG c.val c.val).trans hcell
  have hoff (c d : Fam) (hne : c ≠ d) :
      ‖G c d‖ ≤ eps := by
    have hneVal : c.val ≠ d.val := by
      intro heq
      exact hne (Subtype.ext heq)
    have hb := source_original_full_dyadic_primitive_gram_log_saving434
      S mu hmu hmuPos h j Q Cq c.val d.val
      c.property d.property hneVal i hBIG
      u v n huv hcover V hV hBand hWeight
      L gamma C A K hK hL hgamma hC hExponent
      hQ huLarge huBIG hSW hA hlog
    simpa only [G,eps] using hb
  have hframe :=
    Green64FullPhysicalE.memory_original_finite_cell_gram_schur
      G eps heps hdiag hoff a
  simpa only [G,eps,Fam] using hframe
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualBigCenteredGram -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- TRUE original source03 GLOBAL-cell Gram minus its exact
physical cell probability times the identity. This is an
unconditional off-diagonal operator ERROR estimate, not merely
an upper bound for the frame itself. Every primitive character
level, moving other-prime product and original harmonic law
remains unchanged. -/
theorem source_original_actual_big_centered_gram_unconditional434
    (Cq : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (V : ℝ) (hV : 0 < V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (a : sourceOriginalPrimitiveFamily434 Q → ℂ),
      (∑ c : sourceOriginalPrimitiveFamily434 Q,
        ‖∑ e : sourceOriginalPrimitiveFamily434 Q,
          (sourceOriginalActualPrimitiveGramEntry434
             S mu h j Q c.val e.val -
            if c=e then
              (sourceOriginalRealGramCellMass434 S mu h j:ℂ)
            else 0) * a e‖^2) ≤
      ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) *
         ((K/V)*L^(-B)))^2 *
      (∑ e : sourceOriginalPrimitiveFamily434 Q, ‖a e‖^2) := by
  obtain ⟨K,Y,hK,hGram⟩ :=
    source_original_actual_big_gram_power_unconditional434
      Cq gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hV hBand hWeight a
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let G : Fam → Fam → ℂ := fun c e =>
    sourceOriginalActualPrimitiveGramEntry434
      S mu h j Q c.val e.val
  let nu : ℝ := sourceOriginalRealGramCellMass434 S mu h j
  let eps : ℝ := (K/V)*L^(-B)
  have hLpos : 0 ≤ L := by linarith
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg (div_nonneg hK hV.le)
      (Real.rpow_nonneg hLpos _)
  have hdiag (c : Fam) : G c c = (nu:ℂ) := by
    exact source_original_actual_primitive_gram_diagonal434
      S mu h j Q c.val hBIG
  have hoff (c e : Fam) (hne : c ≠ e) :
      ‖G c e‖ ≤ eps := by
    have hneVal : c.val ≠ e.val := by
      intro h
      exact hne (Subtype.ext h)
    have hb := hGram S mu hmu hmuPos h j Q
      c.val e.val c.property e.property hneVal i hBIG
      L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
      V hV hBand hWeight
    simpa only [G,eps] using hb
  exact source_original_centered_finite_gram_schur434
    G nu eps heps hdiag hoff a
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalGramSynthesis -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Genuine SOURCE03 physical primitive character synthesis
on the indexed product of actual BIG prime labels, using
each character's OWN conductor and the true product D. -/
noncomputable def sourceOriginalPhysicalGramSynthesis434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (Q : ℕ)
    (a : sourceOriginalPrimitiveFamily434 Q → ℂ)
    (p : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  ∑ c : sourceOriginalPrimitiveFamily434 Q,
    c.val.2 (sourceOriginalGramPrimeProduct434 S p :
      ZMod (c.val.1.val+1)) * a c

/-- Algebraic Fubini identity underlying a real synthesis/Gram
pairing, valid even for entirely dependent coefficients. -/
theorem source_original_finite_synthesis_gram_identity434
    {X C : Type} [Fintype X] [Fintype C]
    (w : X → ℝ) (chi : X → C → ℂ)
    (a b : C → ℂ) :
    (∑ x : X, (w x:ℂ) *
      star (∑ c : C, chi x c * a c) *
      (∑ d : C, chi x d * b d)) =
    ∑ c : C, star (a c) *
      ∑ d : C,
        (∑ x : X, (w x:ℂ) * star (chi x c) * chi x d) *
        b d := by
  let F : X → C → C → ℂ := fun x c d =>
    (w x:ℂ)*star (a c)*star (chi x c)*chi x d*b d
  have hpoint (x : X) :
      (w x:ℂ) * star (∑ c : C, chi x c * a c) *
        (∑ d : C, chi x d * b d) =
      ∑ c : C, ∑ d : C, F x c d := by
    have hStar :
        star (∑ c : C, chi x c * a c) =
          ∑ c : C, star (a c)*star (chi x c) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [star_mul]
    rw [hStar]
    calc
      _ = (∑ c : C, (w x:ℂ)*star (a c)*star (chi x c)) *
          (∑ d : C, chi x d*b d) := by
            have hMul :
                (w x:ℂ) * (∑ c : C, star (a c)*star (chi x c)) =
                ∑ c : C, (w x:ℂ)*star (a c)*star (chi x c) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c hc
              ring
            exact congrArg
              (fun z : ℂ => z*(∑ d : C, chi x d*b d)) hMul
      _ = ∑ c : C, ∑ d : C, F x c d := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            dsimp [F]
            ring
  have hComm :
      (∑ x : X, ∑ c : C, ∑ d : C, F x c d) =
      ∑ c : C, ∑ d : C, ∑ x : X, F x c d := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.sum_comm]
  have hRight (c : C) :
      star (a c) *
        (∑ d : C,
          (∑ x : X, (w x:ℂ)*star (chi x c)*chi x d) *
          b d) =
        ∑ d : C, ∑ x : X, F x c d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    calc
      _ = ∑ x : X,
          star (a c) *
            ((w x:ℂ)*star (chi x c)*chi x d)*b d := by
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x : X, F x c d := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [F]
        ring
  calc
    _ = ∑ x : X, ∑ c : C, ∑ d : C, F x c d := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x
    _ = ∑ c : C, ∑ d : C, ∑ x : X, F x c d := hComm
    _ = _ := by
      symm
      apply Finset.sum_congr rfl
      intro c hc
      exact hRight c
end Green64Analytic.CorrelationSquare

end

