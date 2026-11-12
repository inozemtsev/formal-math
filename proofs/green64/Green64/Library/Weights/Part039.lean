module

public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part037
public import Green64.Library.Weights.Part011
public import Mathlib
public import Green64.Library.Weights.Part035
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part002
public import Green64.Library.Analysis.Estimates.Part007
public import Green64.Library.Analysis.Estimates.SourceLowFrequencyFourFactorIntegral
public import Green64.Library.Weights.SourceExceptionalScale
public import Green64.Library.Correlation.Part003
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Weights / Part039

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceLiteralPeelingSquareBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- Physical small-prime peeling residual scalar upper bound, with
all source factor amplitudes and the normalizer K from literal mark
lists, scaled to Y times a fixed log-power (no generic mark cap). -/
theorem source_literal_peeling_square_scaled_budget
    (K L C0 D vmin A C N Y E a : ℝ)
    (nSmall nBig : ℕ)
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hC0 : 0 ≤ C0) (hD : 0 ≤ D) (hv : 0 < vmin)
    (hSmall : (nSmall:ℝ) ≤ C0*Real.log L)
    (hBig : (nBig:ℝ) ≤ C0*Real.log L)
    (hLarge : K*(1+D/(vmin*Real.log 2)) ≤ L)
    (hN : 1 ≤ N) (hNY : N ≤ Y)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hAb : A ≤ L^E) (hCb : C ≤ L^E)
    (hlog : Real.log N ≤ D*L) :
    4*(A*C*(K^(nSmall+nBig+1)*L*
        (1+D/(vmin*Real.log 2))))^2*
        N*(1+Real.log N)^16*Real.exp (-(L^a)) ≤
    4*(1+D)^16*Y*
        L^(4*E+2*(2*C0*Real.log K+2)+16)*
        Real.exp (-(L^a)) := by
  let M : ℝ := K^(nSmall+nBig+1)*L*
      (1+D/(vmin*Real.log 2))
  let Cw : ℝ := 2*C0*Real.log K+2
  have hM : M ≤ L^Cw :=
    source_literal_peeling_logpower_budget K L C0 D vmin
      nSmall nBig hK hL hC0 hD hv
      hSmall hBig hLarge
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hcore : A*C*M ≤ A*C*L^Cw :=
    mul_le_mul_of_nonneg_left hM (mul_nonneg hA hC)
  have hSq : (A*C*M)^2 ≤ (A*C*L^Cw)^2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hcore
  have hStep :
      4*(A*C*M)^2*N*(1+Real.log N)^16*
          Real.exp (-(L^a)) ≤
      4*(A*C*L^Cw)^2*N*(1+Real.log N)^16*
          Real.exp (-(L^a)) := by
    gcongr
  calc
    4*(A*C*M)^2*N*(1+Real.log N)^16*
          Real.exp (-(L^a)) ≤
      4*(A*C*L^Cw)^2*N*(1+Real.log N)^16*
          Real.exp (-(L^a)) := hStep
    _ ≤ 4*(1+D)^16*Y*
        L^(4*E+2*Cw+16)*Real.exp (-(L^a)) :=
      source_square_scale_budget L Y N A C Cw E D a
        hL (by linarith) hN hNY hA hC hE hD hAb hCb hlog
    _ = _ := by simp only [Cw]
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeelingArcSavings -/

section

open Filter Real
namespace Green64Analytic.CorrelationSquare

/-- Fully explicit logarithmic-power loss after summing source
literal small-prime peeling residual over all q≤Q rational centers.
The coefficient K depends only on fixed q0,vmin,tmax. -/
theorem source_literal_peeling_rational_scalar_budget
    (K L C0 D vmin A C N Y E a ArcExp : ℝ)
    (nSmall nBig Q : ℕ)
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (hv : 0 < vmin) (hArc : 0 ≤ ArcExp)
    (hSmall : (nSmall:ℝ) ≤ C0*Real.log L)
    (hBig : (nBig:ℝ) ≤ C0*Real.log L)
    (hLarge : K*(1+D/(vmin*Real.log 2)) ≤ L)
    (hN : 1 ≤ N) (hNY : N ≤ Y)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hAb : A ≤ L^E) (hCb : C ≤ L^E)
    (hlog : Real.log N ≤ D*L)
    (hQ : (Q:ℝ) ≤ L^ArcExp) :
    ((Q*(Q+1):ℕ):ℝ)*
      4*(A*C*(K^(nSmall+nBig+1)*L*
        (1+D/(vmin*Real.log 2))))^2*
        N*(1+Real.log N)^16*Real.exp (-(L^a)) ≤
    Y*(8*(1+D)^16*
       L^(4*E+2*(2*C0*Real.log K+2)+16+2*ArcExp)*
       Real.exp (-(L^a))) := by
  let PeelBound : ℝ :=
     4*(A*C*(K^(nSmall+nBig+1)*L*
        (1+D/(vmin*Real.log 2))))^2*
        N*(1+Real.log N)^16*Real.exp (-(L^a))
  let Cscale : ℝ := 4*E+2*(2*C0*Real.log K+2)+16
  have hLp : 0 < L := by linarith
  have hQcount :=
    source_rational_center_polylog_budget Q L ArcExp hL hArc hQ
  have hPeel : PeelBound ≤
      4*(1+D)^16*Y*L^Cscale*Real.exp (-(L^a)) := by
    simpa only [PeelBound,Cscale] using
      source_literal_peeling_square_scaled_budget
        K L C0 D vmin A C N Y E a nSmall nBig
        hK hL hC0 hD hv hSmall hBig hLarge
        hN hNY hA hC hE hAb hCb hlog
  have hPeelPos : 0 ≤ PeelBound := by
    dsimp [PeelBound]
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
    positivity
  have hPow : L^(Cscale+2*ArcExp) =
      L^Cscale*L^(2*ArcExp) := by
    exact Real.rpow_add hLp Cscale (2*ArcExp)
  have hExpr : ((Q*(Q+1):ℕ):ℝ)*4*(A*C*(K^(nSmall+nBig+1)*L*(1+D/(vmin*Real.log 2))))^2*N*(1+Real.log N)^16*Real.exp (-(L^a)) = ((Q*(Q+1):ℕ):ℝ)*PeelBound := by
    dsimp [PeelBound]
    ring
  rw [hExpr]
  calc
    ((Q*(Q+1):ℕ):ℝ)*PeelBound ≤
       (2*L^(2*ArcExp))*PeelBound :=
         mul_le_mul_of_nonneg_right hQcount hPeelPos
    _ ≤ (2*L^(2*ArcExp))*
       (4*(1+D)^16*Y*L^Cscale*Real.exp (-(L^a))) :=
         mul_le_mul_of_nonneg_left hPeel (by positivity)
    _ = Y*(8*(1+D)^16*
         L^(Cscale+2*ArcExp)*Real.exp (-(L^a))) := by
          rw [hPow]
          ring
    _ = Y*(8*(1+D)^16*
      L^(4*E+2*(2*C0*Real.log K+2)+16+2*ArcExp)*
      Real.exp (-(L^a))) := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## code.SourceParitySquareError -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Literal source choice epsilon(n)=(-1)^(sum of valuations over
the selected prime groups). The exponent counts repeated prime
factors, as required by the original Green64 source. -/
noncomputable def literalSourceParity (P : Finset ℕ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (∑ p ∈ P, n.factorization p)

theorem literal_source_parity_norm_one (P : Finset ℕ) (n : ℕ) :
    ‖literalSourceParity P n‖ = 1 := by
  simp [literalSourceParity, norm_pow]

/-- The exact same L² estimate holds for the source common parity
choice epsilon at either endpoint, or for epsilon=1. This identity
does not assume that the marked source core is multiplicative. -/
theorem literal_source_parity_preserves_square_error
    (N : ℕ) (S P : Finset ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
        ‖literalSourceParity P n * F n‖^2) =
    (∑ n ∈ sourceSquareExceptionalSupport N S,
        ‖F n‖^2) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul, literal_source_parity_norm_one, one_mul]

/-- The second permitted source choice epsilon=1 is also
exactly neutral on the physical square-exception L² norm. -/
theorem literal_source_trivial_parity_preserves_square_error
    (N : ℕ) (S : Finset ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ sourceSquareExceptionalSupport N S,
        ‖(1:ℂ) * F n‖^2) =
    (∑ n ∈ sourceSquareExceptionalSupport N S,
        ‖F n‖^2) := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalMarkedResidual -/

section

/-! Explicit source-structured major-arc marked residual: outside factor,
all small/big marked weights, multiplicity-counted parity and the
rational-character gcd restriction. This is a candidate literal d_{r'};
its equality with the extracted coefficient of the original
physical Fourier polynomial requires a separate source identity. -/

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

noncomputable def sourcePhysicalMarkedResidual
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (r : ℕ) : ℂ :=
  if Nat.gcd r den = d0 then
    c (sourceOutsidePart G r) *
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r *
      χ (r / d0) * literalSourceParity Parity r * sourceUnitTwist r σ
  else 0

/-- The genuinely marked source d_{r'} has the required coefficient
bound, including all small/big groups, original outside c, rational
character, exact gcd filter, and both permitted unit-parity choices. -/
theorem source_physical_marked_residual_bound
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k ≤ tmax → vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
          (∀ n, ‖c n‖ ≤ C) →
        ∀ (den d0 q : ℕ) (χ : DirichletCharacter ℂ q)
          (σ : ℝ) (r : ℕ),
          ‖sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k G Parity c den d0 q χ σ r‖ ≤
          C * K^(Fintype.card ι + Fintype.card β + 1) := by
  obtain ⟨K,hK,hWeight⟩ :=
    source_literal_weight_uniform_all_groups q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    G Parity c hc den d0 q χ σ r
  have hW : ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
      ts tb b k r‖ ≤ K^(Fintype.card ι + Fintype.card β + 1) :=
    hWeight S Ts Tb Vs Vsmall Vbig ts tb b k r
      hk hVs hts htb hVsmall hVbig hb
  have hχ : ‖χ (r / d0)‖ ≤ 1 := χ.norm_le_one (r / d0 : ZMod q)
  have hε : ‖literalSourceParity Parity r‖ = 1 :=
    literal_source_parity_norm_one Parity r
  have htw : ‖sourceUnitTwist r σ‖ = 1 := sourceUnitTwist_norm r σ
  have hK0 : 0 ≤ K^(Fintype.card ι + Fintype.card β + 1) := by
    positivity
  unfold sourcePhysicalMarkedResidual
  split_ifs with hgcd
  · calc
      ‖c (sourceOutsidePart G r) *
          literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r *
          χ (r / d0) * literalSourceParity Parity r * sourceUnitTwist r σ‖ =
        ‖c (sourceOutsidePart G r)‖ *
        ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r‖ *
        ‖χ (r / d0)‖ := by
          simp only [norm_mul, hε, htw, mul_one]
      _ ≤ C * K^(Fintype.card ι + Fintype.card β + 1) * 1 := by
          gcongr
          exact hc _
      _ = _ := by ring
  · simp only [norm_zero]
    positivity
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPhysicalFrequencyShift -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare

/-! The original source marked residual absorbs a real Mellin
frequency shift into its existing sigmaR parameter. The literal
gcd filter, signs, ordered marks and character are unchanged. -/
theorem source_actual_unit_twist_as_phase (n : ℕ) (sigma : ℝ) :
    sourceUnitTwist n sigma = sourcePhase n sigma := by
  unfold sourceUnitTwist sourcePhase
  congr 1
  ring

theorem source_actual_physical_residual_frequency_shift
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
    (sigmaR nu : ℝ) (r : ℕ) :
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR r *
      sourcePhase r nu =
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR (sigmaR+nu) r := by
  by_cases hGcd : Nat.gcd r den = d0
  · simp only [sourcePhysicalMarkedResidual, if_pos hGcd]
    rw [source_actual_unit_twist_as_phase,
      source_actual_unit_twist_as_phase,
      sourcePhase_add r sigmaR nu]
    ring
  · simp only [sourcePhysicalMarkedResidual, if_neg hGcd, zero_mul]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPhysicalTranslatedEnergy -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare

noncomputable def sourceActualRetainedFrequencyTwist
    (coeff : ℕ → ℂ) (nu : ℝ) (n : ℕ) : ℂ :=
  coeff n * sourcePhase n nu

theorem source_actual_physical_translated_energy
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
    (sigmaR : ℝ)
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs : ℕ → ℂ) {qM qL : ℕ}
    (chiM : DirichletCharacter ℂ qM)
    (chiL : DirichletCharacter ℂ qL)
    (sigma0 sigma1 T nu : ℝ) :
    (∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b alpha bs
        (fun p => chiL p)
        (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR sigmaR)
        chiM sigma0 sigma1 (t + nu)‖ ^ 2) =
    ∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b alpha
        (sourceActualRetainedFrequencyTwist bs nu) (fun p => chiL p)
        (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR (sigmaR + nu))
        chiM (sigma0 + nu) (sigma1 + nu) t‖ ^ 2 := by
  have hUnit (n : ℕ) (sigma : ℝ) :
      sourceUnitTwist n sigma = sourcePhase n sigma := by
    unfold sourceUnitTwist sourcePhase
    congr 1
    ring
  have hResidual (r : ℕ) :
      sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR r *
        sourcePhase r nu =
      sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR (sigmaR + nu) r := by
    by_cases hGcd : Nat.gcd r den = d0
    · simp only [sourcePhysicalMarkedResidual, if_pos hGcd]
      rw [hUnit, hUnit, sourcePhase_add r sigmaR nu]
      ring
    · simp only [sourcePhysicalMarkedResidual, if_neg hGcd, zero_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hs :
      (∑ ps ∈ small, bs ps * (ps : ℂ)⁻¹ * sourcePhase ps (t + nu)) =
      ∑ ps ∈ small, sourceActualRetainedFrequencyTwist bs nu ps *
        (ps : ℂ)⁻¹ * sourcePhase ps t := by
    apply Finset.sum_congr rfl
    intro ps hps
    rw [sourcePhase_add ps t nu]
    dsimp [sourceActualRetainedFrequencyTwist]
    ring
  have hp :
      (∑ p ∈ long, chiL p * (p : ℂ)⁻¹ *
        sourcePhase p (sigma1 + (t + nu))) =
      ∑ p ∈ long, chiL p * (p : ℂ)⁻¹ *
        sourcePhase p ((sigma1 + nu) + t) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [show sigma1 + (t + nu) = (sigma1 + nu) + t by ring]
  have hm :
      (∑ m ∈ Finset.Icc a b, alpha m * chiM m * (m : ℂ)⁻¹ *
        sourcePhase m (sigma0 + (t + nu))) =
      ∑ m ∈ Finset.Icc a b, alpha m * chiM m * (m : ℂ)⁻¹ *
        sourcePhase m ((sigma0 + nu) + t) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [show sigma0 + (t + nu) = (sigma0 + nu) + t by ring]
  have hr :
      (∑ r ∈ R,
        sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR sigmaR r *
          (r : ℂ)⁻¹ * sourcePhase r (t + nu)) =
      ∑ r ∈ R,
        sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR (sigmaR + nu) r *
          (r : ℂ)⁻¹ * sourcePhase r t := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [sourcePhase_add r t nu]
    calc
      sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR sigmaR r *
          (r : ℂ)⁻¹ * (sourcePhase r t * sourcePhase r nu) =
        (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR sigmaR r *
          sourcePhase r nu) * (r : ℂ)⁻¹ * sourcePhase r t := by ring
      _ = _ := by rw [hResidual]
  congr 2
  unfold sourceFourFactorAt
  rw [hs, hp, hm, hr]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPhysicalFourierL1MeanSquare -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.CorrelationMellin

/-- Physical specialization of the continuous Fourier L¹/L² bridge.
The required uniform estimate is stated for the same literal physical
family after its exact retained-frequency parameter shift. -/
theorem source_actual_physical_fourier_l1_mean_square
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (marks : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (groups Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
    (sigmaR : ℝ)
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs : ℕ → ℂ) {qM qL : ℕ}
    (chiM : DirichletCharacter ℂ qM)
    (chiL : DirichletCharacter ℂ qL)
    (sigma0 sigma1 T : ℝ)
    (S : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ)
    (B mass : ℝ)
    (hB : 0 ≤ B) (hmass : 0 ≤ mass)
    (hFreq : Continuous freq)
    (hK : IntegrableOn K S)
    (hUniform : ∀ᵐ ξ ∂volume.restrict S,
      (∫ t in Set.Icc (-T) T,
        ‖sourceFourFactorAt small long R a b alpha
          (sourceActualRetainedFrequencyTwist bs (freq ξ))
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual marks Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k groups Parity c den d0 q chiR
              (sigmaR + freq ξ))
          chiM (sigma0 + freq ξ) (sigma1 + freq ξ) t‖ ^ 2) ≤ B)
    (hKmass : (∫ ξ in S, ‖K ξ‖) ≤ mass)
    (ha : 1 ≤ a)
    (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    ‖∫ ξ in S, K ξ •
      sourceActualFourDyadL2Lift small long R a b T alpha bs
        (fun p => chiL p)
        (sourcePhysicalMarkedResidual marks Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k groups Parity c den d0 q chiR sigmaR)
        chiM sigma0 sigma1 freq ξ‖ ^ 2
      ≤ mass ^ 2 * B := by
  have hOriginal : ∀ᵐ ξ ∂volume.restrict S,
      (∫ t in Set.Icc (-T) T,
        ‖sourceFourFactorAt small long R a b alpha bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual marks Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k groups Parity c den d0 q chiR sigmaR)
          chiM sigma0 sigma1 (t + freq ξ)‖ ^ 2) ≤ B := by
    filter_upwards [hUniform] with ξ hξ
    rw [source_actual_physical_translated_energy
      marks Ts Tb q0 Vs Vsmall Vbig ts tb coef k
      groups Parity c den d0 q chiR sigmaR
      small long R a b alpha bs chiM chiL
      sigma0 sigma1 T (freq ξ)]
    exact hξ
  exact source_actual_fourdyad_fourier_l1_mean_square
    small long R a b T alpha bs (fun p => chiL p)
    (sourcePhysicalMarkedResidual marks Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k groups Parity c den d0 q chiR sigmaR)
    chiM sigma0 sigma1 S K freq B mass hB hmass hFreq hK
    hOriginal hKmass ha hs hp hr

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualRetainedFrequencyBudget -/

section

namespace Green64Analytic.CorrelationMellin

theorem source_actual_retained_frequency_twist_norm
    (coeff : ℕ → ℂ) (nu : ℝ) (n : ℕ) :
    ‖sourceActualRetainedFrequencyTwist coeff nu n‖ = ‖coeff n‖ := by
  simp [sourceActualRetainedFrequencyTwist, sourcePhase_norm]

/-- A fixed log-power Fourier-frequency budget can be absorbed into
one enlarged existing source Mellin-shift exponent. -/
theorem source_actual_retained_frequency_shift_budget
    (L sigma nu : ℝ) (s f : ℕ)
    (hL : 2 ≤ L)
    (hSigma : |sigma| ≤ L ^ s)
    (hNu : |nu| ≤ L ^ f) :
    |sigma + nu| ≤ L ^ (max s f + 1) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hs : L ^ s ≤ L ^ (max s f) :=
    pow_le_pow_right₀ hL1 (Nat.le_max_left s f)
  have hf : L ^ f ≤ L ^ (max s f) :=
    pow_le_pow_right₀ hL1 (Nat.le_max_right s f)
  calc
    |sigma + nu| ≤ |sigma| + |nu| := abs_add_le _ _
    _ ≤ L ^ s + L ^ f := add_le_add hSigma hNu
    _ ≤ 2 * L ^ (max s f) := by linarith
    _ ≤ L * L ^ (max s f) :=
      mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 _)
    _ = L ^ (max s f + 1) := by rw [pow_succ]; ring

/-- Simultaneously absorb a retained Fourier frequency into the two
source endpoint shifts. -/
theorem source_actual_two_retained_shift_budgets
    (L sigma0 sigma1 nu : ℝ) (s0 s1 f : ℕ)
    (hL : 2 ≤ L)
    (hSigma0 : |sigma0| ≤ L ^ s0)
    (hSigma1 : |sigma1| ≤ L ^ s1)
    (hNu : |nu| ≤ L ^ f) :
    |sigma0 + nu| ≤ L ^ (max s0 f + 1) ∧
    |sigma1 + nu| ≤ L ^ (max s1 f + 1) :=
  ⟨source_actual_retained_frequency_shift_budget
      L sigma0 nu s0 f hL hSigma0 hNu,
    source_actual_retained_frequency_shift_budget
      L sigma1 nu s1 f hL hSigma1 hNu⟩

end Green64Analytic.CorrelationMellin

end

/-! ## SourcePhysicalCollapsedResidualNorm -/

section

/-! Coefficient-square bound for the explicitly source-structured
residual constructor (literal marks/outside part, parity, character and
rational gcd class), without a postulated h_d. Equality of this
constructor to the *extracted* source Fourier residual is not proved here. -/

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

theorem source_physical_residual_true_dyadic_square_norm
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 1 ≤ K ∧
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
      (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
      (ts : ι → ℕ) (tb : β → ℕ)
      (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖b lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
        (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (χ : DirichletCharacter ℂ q)
        (σ : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
        0 < M0 → 0 < R0 → 0 ≤ A →
        M ⊆ Finset.Icc M0 (2*M0) →
        R ⊆ Finset.Icc R0 (2*R0) →
        (∀ m ∈ M, ‖alpha m‖ ≤ A) →
        (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
        (∑ n ∈ (M.product R).image (fun z => z.1*z.2),
          ‖sourceResidualProductCoeff M R
            (sourceAlphaCharacterCoefficient alpha chiM sigma0)
            (sourceMarkedResidualCoefficient
              (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
                ts tb b k G Parity c den d0 q χ σ)) n‖^2) ≤
          ((A*(C*K^(Fintype.card ι+Fintype.card β+1))) /
            ((M0*R0:ℕ):ℝ))^2 * ((4*(M0*R0):ℕ):ℝ) *
            (1+Real.log ((4*(M0*R0):ℕ):ℝ))^3 := by
  obtain ⟨K,hK,hBound⟩ :=
    source_physical_marked_residual_bound
      q0 vmin tmax hq0 hq1 hv C hC
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    G Parity c hc den d0 q χ σ M R M0 R0 alpha chiM sigma0 A
    hM0 hR0 hA hM hR ha hchi
  let D : ℝ := C*K^(Fintype.card ι+Fintype.card β+1)
  let d : ℕ → ℂ := sourcePhysicalMarkedResidual S Ts Tb
    q0 Vs Vsmall Vbig ts tb b k G Parity c den d0 q χ σ
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hd (r : ℕ) (_hr : r ∈ R) : ‖d r‖ ≤ D := by
    exact hBound S Ts Tb Vs Vsmall Vbig ts tb b k
      hk hVs hts htb hVsmall hVbig hb
      G Parity c hc den d0 q χ σ r
  have hMass := source_residual_true_dyadic_square_norm
    M R M0 R0 alpha chiM d sigma0 A D
    hM0 hR0 hA hD hM hR ha hchi hd
  simpa only [D, d] using hMass
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePhysicalResidualUniformC -/

section

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Uniform in the source coefficient bound C. Unlike a fixed-C
specialization, this remains applicable when C = L^C₀ grows with L.
The single K comes from the *previously verified* literal mark-weight
bound and is independent of C, all characters and the gcd class. -/
theorem source_physical_marked_residual_uniform_C
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k ≤ tmax → vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖coef lists‖ ≤ 1) →

        ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
          (∀ n, ‖c n‖ ≤ C) →
        ∀ (den d0 q : ℕ) (χ : DirichletCharacter ℂ q)
          (σ : ℝ) (r : ℕ),
          ‖sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c den d0 q χ σ r‖ ≤
          C * K^(Fintype.card ι+Fintype.card β+1) := by
  obtain ⟨K,hK,hWeight⟩ :=
    source_literal_weight_uniform_all_groups q0 vmin tmax
      hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro C hC ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q χ σ r
  have hW : ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k r‖ ≤
      K^(Fintype.card ι+Fintype.card β+1) :=
    hWeight S Ts Tb Vs Vsmall Vbig ts tb coef k r
      hk hVs hts htb hVsmall hVbig hcoef
  have hχ : ‖χ (r / d0)‖ ≤ 1 :=
    χ.norm_le_one (r / d0 : ZMod q)
  have hParity : ‖literalSourceParity Parity r‖ = 1 :=
    literal_source_parity_norm_one Parity r
  have hTwist : ‖sourceUnitTwist r σ‖ = 1 :=
    sourceUnitTwist_norm r σ

  have hKnonneg :
      0 ≤ K^(Fintype.card ι+Fintype.card β+1) := by positivity
  unfold sourcePhysicalMarkedResidual
  split_ifs with hgcd
  · calc
      ‖c (sourceOutsidePart G r) *
        literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb coef k r *
        χ (r/d0) * literalSourceParity Parity r *
        sourceUnitTwist r σ‖ =
        ‖c (sourceOutsidePart G r)‖ *
        ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k r‖ * ‖χ (r/d0)‖ := by
          simp only [norm_mul, hParity, hTwist, mul_one]
      _ ≤ C * K^(Fintype.card ι+Fintype.card β+1) * 1 := by
          gcongr
          exact hc _
      _ = _ := by ring
  · simp only [norm_zero]
    positivity
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualPhysicalResidualCoeffBudget -/

section

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare

/-! The real original residual coefficient, including gcd filter,
all marked weights, characters and parity, has one UNIFORM
logarithmic-power budget at the source group cardinality scale. -/
theorem source_actual_physical_residual_polylog_coeff_budget
    (q0 vmin C0 : ℝ) (tmax ec : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ K : ℝ, ∃ g : ℕ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ L : ℝ, max 3 K ≤ L →
        (Fintype.card ι:ℝ) ≤ C0*Real.log L →
        (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
        (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (r : ℕ),
        ‖sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k G Parity c den d0 q chiR sigmaR r‖ ≤
          L^(ec+g) := by
  obtain ⟨K,hK,hCoef⟩ :=
    source_physical_marked_residual_uniform_C
      q0 vmin tmax hq0 hq1 hv
  obtain ⟨g,hGroups⟩ :=
    source_literal_group_card_uniform_nat_log_budget
      K C0 hK hC0
  refine ⟨K,g,hK,?_⟩
  intro ι β _ _ _ _ L hL hSmall hBig
    C hC hCBudget S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR r
  have hKpow : K^(Fintype.card ι+Fintype.card β+1) ≤ L^g :=
    hGroups L hL (Fintype.card ι) (Fintype.card β)
      hSmall hBig
  have hBase := hCoef C hC S Ts Tb Vs Vsmall Vbig
    ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR r
  have hKpos : 0 ≤ K^(Fintype.card ι+Fintype.card β+1) := by positivity
  have hLpos : 0 ≤ L := by
    have hh := (le_max_left (3:ℝ) K).trans hL
    linarith
  calc
    _ ≤ C*K^(Fintype.card ι+Fintype.card β+1) := hBase
    _ ≤ L^ec*K^(Fintype.card ι+Fintype.card β+1) :=
      mul_le_mul_of_nonneg_right hCBudget hKpos
    _ ≤ L^ec*L^g :=
      mul_le_mul_of_nonneg_left hKpow (pow_nonneg hLpos _)
    _ = L^(ec+g) := by rw [pow_add]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalPhysicalPolylog -/

section

/-! Source-physical specialization of the exceptional-residual logarithmic
energy budget. The coefficient bound is derived from the literal marked
outside part, character, parity and every source mark group. -/
namespace Green64Analytic.CorrelationMellin

theorem eventually_source_exceptional_physical_sparse_polylog
    (a b As Cs q0 vmin : ℝ) (tmax : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1)
    (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ L : ℝ in Filter.atTop, ∀ (P Y : ℕ),
        1 ≤ P → 1 ≤ Y →
        Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
        (P:ℝ) ≤ Real.exp (L^b) →
        Real.exp (L/2) ≤ (Y:ℝ) →
        (Y:ℝ) ≤ Real.exp (2*L) →
        ∀ {κ : Type*} {ι β : Type}
          [Fintype κ] [DecidableEq κ]
          [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
        ∀ (witness sample : κ → ℝ) (s : Finset ℕ),

        (∀ p ∈ s, Nat.Prime p) →
        s ⊆ Finset.Icc P (2*P) →
        ∀ (bs : ℕ → ℂ),
        (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
        (∀ i, |witness i| ≤ (Y:ℝ)) →
        (∀ i j, i ≠ j → 1 ≤ |witness i-witness j|) →
        (∀ i, |sample i| ≤ (Y:ℝ)) →
        (∀ i j, i ≠ j → 1 ≤ |sample i-sample j|) →
        (∀ i : κ, L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
                sourcePhase p.val (witness i)‖) →
        ∀ (C : ℝ), 0 ≤ C →
        ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
          (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
          (ts : ι → ℕ) (tb : β → ℕ)
          (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k ≤ tmax → vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖coef lists‖ ≤ 1) →
        ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
        (∀ n, ‖c n‖ ≤ C) →

        ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
          (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
          (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
        0 < M0 → 0 < R0 → 0 ≤ A →
        ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
        (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
        M ⊆ Finset.Icc M0 (2*M0) →
        R ⊆ Finset.Icc R0 (2*R0) →
        (∀ m ∈ M, ‖alpha m‖ ≤ A) →
        (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
        (∑ i : κ,
          ‖(∑ m ∈ M, alpha m * chiM m * (m:ℂ)⁻¹ *
               sourcePhase m (sigma0+sample i)) *
            (∑ r ∈ R,
               sourcePhysicalMarkedResidual
                 S Ts Tb q0 Vs Vsmall Vbig ts tb coef k G Parity c
                 den d0 q chiR sigmaR r *
               (r:ℂ)⁻¹ * sourcePhase r (sample i))‖^2) ≤
          3584*(A*(C*K^(Fintype.card ι+Fintype.card β+1)))^2*
             (1+Real.log (4*(Y:ℝ)))^4 := by
  obtain ⟨K,hK,hBound⟩ :=
    source_physical_marked_residual_uniform_C
      q0 vmin tmax hq0 hq1 hv
  have hEvent := eventually_source_exceptional_residual_sparse_polylog
    a b As Cs ha hab hb hAs hCs
  refine ⟨K,hK,?_⟩

  filter_upwards [hEvent] with L hE P Y hP hY hPmin hPmax
    hYmin hYmax κ ι β _ _ _ _ _ _
    witness sample s hp hs bs hbs hwt hwsep hst hssep hlarge
    C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0 alpha chiM
    sigma0 A hM0 hR0 hA hUY hUlower hM hR ha hchi
  let D : ℝ := C*K^(Fintype.card ι+Fintype.card β+1)
  let d : ℕ → ℂ :=
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd (r : ℕ) (_hr : r ∈ R) : ‖d r‖ ≤ D :=
    hBound C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc den d0 q chiR sigmaR r
  have hOutput := hE P Y hP hY hPmin hPmax hYmin hYmax
    witness sample s hp hs bs hbs hwt hwsep hst hssep hlarge
    M R M0 R0 alpha chiM d sigma0 A D
      hM0 hR0 hA hD hUY hUlower hM hR ha hchi hd
  simpa only [D,d] using hOutput
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalIntervalSup -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

/-! The two independent times used in the source proof come from
short-prime witnesses and residual maxima on the same unit intervals.
Compactness supplies the latter; mod-three separation allows reuse of
the unconditional sparse frame inequality. -/

/-- A continuous complex polynomial attains its squared-norm maximum
on every *closed* unit interval. -/
theorem source_unit_interval_max_exists
    (F : ℝ → ℂ) (hF : Continuous F) (j : ℤ) :
    ∃ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      ∀ u ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        ‖F u‖^2 ≤ ‖F t‖^2 := by
  have hNonempty : (Set.Icc (j:ℝ) ((j:ℝ)+1)).Nonempty := by
    refine ⟨(j:ℝ), ?_⟩
    simp
  obtain ⟨t,ht,hMax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (j:ℝ) ((j:ℝ)+1))).exists_isMaxOn
      hNonempty ((hF.norm.pow 2).continuousOn)
  exact ⟨t,ht,fun u hu => hMax hu⟩

/-- Each unit interval contributes at most its attained maximum to
the real Mellin squared energy: the interval has length exactly one. -/
theorem source_unit_interval_integral_le_max

    (F : ℝ → ℂ) (hF : Continuous F) (j : ℤ) (t : ℝ)
    (hMax : ∀ u ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        ‖F u‖^2 ≤ ‖F t‖^2) :
    (∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
        ‖F t‖^2 := by
  have hInt : IntegrableOn (fun u : ℝ => ‖F u‖^2)
      (Set.Icc (j:ℝ) ((j:ℝ)+1)) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hμ : volume (Set.Icc (j:ℝ) ((j:ℝ)+1)) ≠ ⊤ :=
    (measure_Icc_lt_top : volume
      (Set.Icc (j:ℝ) ((j:ℝ)+1)) < ⊤).ne
  have hConst : IntegrableOn (fun _ : ℝ => ‖F t‖^2)
      (Set.Icc (j:ℝ) ((j:ℝ)+1)) := integrableOn_const hμ
  have hMono :
      (∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
      (∫ _u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) :=
    setIntegral_mono_on hInt hConst measurableSet_Icc hMax
  calc
    _ ≤ (∫ _u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) := hMono
    _ = ‖F t‖^2 := by
      rw [setIntegral_const]
      change (volume (Set.Icc (j:ℝ) ((j:ℝ)+1))).toReal *
        ‖F t‖^2 = ‖F t‖^2
      rw [Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith :
        0 ≤ ((j:ℝ)+1)-(j:ℝ))]
      ring

/-- Indices congruent modulo three give disjoint separated real
samples even when each point is chosen independently on its interval. -/
theorem source_unit_samples_separated_mod_three
    (j k : ℤ) (hmod : j % 3 = k % 3) (hjk : j ≠ k)
    (tj tk : ℝ)
    (htj : tj ∈ Set.Icc (j:ℝ) ((j:ℝ)+1))
    (htk : tk ∈ Set.Icc (k:ℝ) ((k:ℝ)+1)) :
    1 ≤ |tj-tk| := by
  have hIdx : j+3 ≤ k ∨ k+3 ≤ j := by omega
  rcases hIdx with hjk' | hkj'
  · have hr : (j:ℝ)+3 ≤ (k:ℝ) := by exact_mod_cast hjk'
    have hneg : tj-tk ≤ -2 := by
      rcases htj with ⟨_,hupper⟩
      rcases htk with ⟨hlower,_⟩
      linarith
    rw [abs_of_nonpos (by linarith : tj-tk ≤ 0)]
    linarith
  · have hr : (k:ℝ)+3 ≤ (j:ℝ) := by exact_mod_cast hkj'
    have hpos : 2 ≤ tj-tk := by
      rcases htj with ⟨hlower,_⟩
      rcases htk with ⟨_,hupper⟩
      linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ tj-tk)]
    linarith

/-- The sum of energies on a finite set of occupied unit intervals
is bounded by the sum of the genuine attained maxima. -/
theorem source_finite_unit_interval_energy_le_max
    (J : Finset ℤ) (F : ℝ → ℂ) (hF : Continuous F)
    (sample : ℤ → ℝ)
    (hSample : ∀ j ∈ J,
      sample j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1))
    (hMax : ∀ j ∈ J, ∀ u ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      ‖F u‖^2 ≤ ‖F (sample j)‖^2) :
    (∑ j ∈ J,
      ∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
    ∑ j ∈ J, ‖F (sample j)‖^2 := by
  apply Finset.sum_le_sum
  intro j hj
  exact source_unit_interval_integral_le_max
    F hF j (sample j) (hMax j hj)

/-- The canonical (choice-based) maximizer, with no additional
hypothesis on the residual polynomial beyond continuity. -/
noncomputable def sourceUnitMaximizer
    (F : ℝ → ℂ) (hF : Continuous F) (j : ℤ) : ℝ :=
  Classical.choose (source_unit_interval_max_exists F hF j)

theorem sourceUnitMaximizer_mem
    (F : ℝ → ℂ) (hF : Continuous F) (j : ℤ) :
    sourceUnitMaximizer F hF j ∈
      Set.Icc (j:ℝ) ((j:ℝ)+1) :=
  (Classical.choose_spec (source_unit_interval_max_exists F hF j)).1

theorem sourceUnitMaximizer_is_max
    (F : ℝ → ℂ) (hF : Continuous F) (j : ℤ) :
    ∀ u ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      ‖F u‖^2 ≤ ‖F (sourceUnitMaximizer F hF j)‖^2 :=
  (Classical.choose_spec (source_unit_interval_max_exists F hF j)).2

theorem source_finite_unit_interval_energy_le_selected_max
    (J : Finset ℤ) (F : ℝ → ℂ) (hF : Continuous F) :
    (∑ j ∈ J,
      ∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
    ∑ j ∈ J, ‖F (sourceUnitMaximizer F hF j)‖^2 :=
  source_finite_unit_interval_energy_le_max J F hF
    (sourceUnitMaximizer F hF)
    (fun j _ => sourceUnitMaximizer_mem F hF j)
    (fun j _ => sourceUnitMaximizer_is_max F hF j)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalModThree -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Three-coloring of actual integer unit intervals. No abstract
separation condition is introduced: integer congruence gives it. -/

theorem source_mod_three_sum_partition
    (J : Finset ℤ) (f : ℤ → ℝ) :
    (∑ j ∈ J, f j) =
    ∑ c ∈ Finset.Icc (0:ℤ) 2,
      ∑ j ∈ J.filter (fun j => j % 3 = c), f j := by
  classical
  calc
    _ = ∑ j ∈ J, ∑ c ∈ Finset.Icc (0:ℤ) 2,
          if j % 3 = c then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hmod : j % 3 ∈ Finset.Icc (0:ℤ) 2 := by
        simp only [Finset.mem_Icc]
        omega
      simp [hmod]
    _ = ∑ c ∈ Finset.Icc (0:ℤ) 2,
          ∑ j ∈ J, if j % 3 = c then f j else 0 :=
        Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

theorem source_mod_three_sum_bound
    (J : Finset ℤ) (f : ℤ → ℝ) (B : ℝ)

    (hclass : ∀ c ∈ Finset.Icc (0:ℤ) 2,
      (∑ j ∈ J.filter (fun j => j % 3 = c), f j) ≤ B) :
    (∑ j ∈ J, f j) ≤ 3*B := by
  rw [source_mod_three_sum_partition]
  calc
    _ ≤ ∑ c ∈ Finset.Icc (0:ℤ) 2, B := by
      apply Finset.sum_le_sum
      intro c hc
      exact hclass c hc
    _ = 3*B := by
      have hset : Finset.Icc (0:ℤ) 2 = {0,1,2} := by decide
      simp [hset]

/-- Choosing arbitrary samples on unit intervals within one residue
class produces one-separated real times. -/
theorem source_mod_three_class_samples_separated
    (J : Finset ℤ) (c : ℤ) (sample : ℤ → ℝ)
    (hSample : ∀ j ∈ J,
       sample j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    ∀ i k : {j : ℤ // j ∈ J.filter (fun j => j % 3 = c)},
      i ≠ k → 1 ≤ |sample i.val - sample k.val| := by
  intro i k hik
  have hi : i.val ∈ J ∧ i.val % 3 = c :=
    Finset.mem_filter.mp i.property
  have hk : k.val ∈ J ∧ k.val % 3 = c :=
    Finset.mem_filter.mp k.property
  have hdiff : i.val ≠ k.val := by
    intro h
    apply hik
    exact Subtype.ext h
  exact source_unit_samples_separated_mod_three i.val k.val
    (hi.2.trans hk.2.symm) hdiff _ _
    (hSample i.val hi.1) (hSample k.val hk.1)

/-- The exact missing finite-interval passage after obtaining one
source sparse estimate for each of the three residue classes. -/
theorem source_unit_interval_energy_from_three_sparse_classes
    (J : Finset ℤ) (F : ℝ → ℂ) (hF : Continuous F)
    (B : ℝ)
    (hclass : ∀ c ∈ Finset.Icc (0:ℤ) 2,
      (∑ j ∈ J.filter (fun j => j % 3 = c),
         ‖F (sourceUnitMaximizer F hF j)‖^2) ≤ B) :
    (∑ j ∈ J,
      ∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
    3*B := by
  exact (source_finite_unit_interval_energy_le_selected_max
    J F hF).trans
      (source_mod_three_sum_bound J
        (fun j => ‖F (sourceUnitMaximizer F hF j)‖^2) B hclass)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalIntervalPhysical -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare

/-- The actual fixed-gcd, fixed-character Mellin residual pair.
No replacement by a free abstract function or unproved coefficient. -/
noncomputable def sourcePhysicalResidualAt
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q) (sigmaR : ℝ)
    (M R : Finset ℕ) (alpha chiM : ℕ → ℂ)
    (sigma0 t : ℝ) : ℂ :=
  (∑ m ∈ M, alpha m * chiM m * (m:ℂ)⁻¹ *
       sourcePhase m (sigma0+t)) *
  (∑ r ∈ R,
     sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
       ts tb coef k G Parity c den d0 q chiR sigmaR r *
      (r:ℂ)⁻¹ * sourcePhase r t)


/-- Continuity of the exact marked residual Dirichlet polynomial. -/
theorem sourcePhysicalResidualAt_continuous
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q) (sigmaR : ℝ)
    (M R : Finset ℕ) (alpha chiM : ℕ → ℂ)
    (sigma0 : ℝ) :
    Continuous (fun t => sourcePhysicalResidualAt S Ts Tb q0 Vs
      Vsmall Vbig ts tb coef k G Parity c den d0 q chiR
      sigmaR M R alpha chiM sigma0 t) := by
  unfold sourcePhysicalResidualAt
  apply Continuous.mul
  · apply continuous_finset_sum
    intro m hm
    exact continuous_const.mul (sourcePhase_continuous m sigma0)
  · apply continuous_finset_sum
    intro r hr
    have hc : Continuous (fun _t : ℝ =>
      sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR r * (r:ℂ)⁻¹) :=
      continuous_const
    have hp : Continuous (fun t : ℝ => sourcePhase r t) := by
      simpa only [zero_add] using sourcePhase_continuous r 0
    exact hc.mul hp

/-- Source time range on the whole closed unit interval from the
original exceptional interval index. -/
theorem source_unit_time_range_from_index
    (j : ℤ) (Y t : ℝ)
    (hIndex : |(j:ℝ)|+1 ≤ Y)
    (ht : t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    |t| ≤ Y := by
  have hj : |(j:ℝ)| ≤ Y-1 := by linarith
  have hbounds := abs_le.mp hj
  rcases ht with ⟨hlo,hhi⟩
  apply abs_le.mpr
  constructor <;> linarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalClassBridge -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-- A class of integer unit intervals is indexed once, as a subtype of
the genuine finite set; this introduces no new representations. -/
theorem source_class_subtype_sum
    (J : Finset ℤ) (c : ℤ) (f : ℤ → ℝ) :
    (∑ i : {j : ℤ // j ∈ J.filter (fun j => j % 3 = c)}, f i.val) =
      ∑ j ∈ J.filter (fun j => j % 3 = c), f j := by
  classical
  let T : Finset ℤ := J.filter (fun j => j % 3 = c)
  letI : Fintype {j : ℤ // j ∈ T} := Finset.fintypeCoeSort T
  simpa only [T] using (Finset.sum_coe_sort T f)

/-- Once the class sparse estimates are available, this transports
them through compactness and the exact mod-three partition to the
REAL sum of squared residual integrals on occupied intervals. -/
theorem source_interval_energy_of_class_subtype_bounds
    (J : Finset ℤ) (F : ℝ → ℂ) (hF : Continuous F)
    (B : ℝ)
    (hclass : ∀ c ∈ Finset.Icc (0:ℤ) 2,
      (∑ i : {j : ℤ // j ∈ J.filter (fun j => j % 3 = c)},
        ‖F (sourceUnitMaximizer F hF i.val)‖^2) ≤ B) :
    (∑ j ∈ J,
      ∫ u in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F u‖^2) ≤
    3*B := by
  apply source_unit_interval_energy_from_three_sparse_classes J F hF B
  intro c hc
  rw [← source_class_subtype_sum]
  exact hclass c hc
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalPhysicalIntervalEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare

/-! The full exceptional-interval (rather than selected-point) energy
for the actual fixed-character, fixed-gcd physical residual. -/
theorem eventually_source_exceptional_physical_interval_energy
    (a b As Cs q0 vmin : ℝ) (tmax : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1)
    (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ᶠ L : ℝ in Filter.atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ (J : Finset ℤ) (witness : ℤ → ℝ) (s : Finset ℕ),
      (∀ j ∈ J, |(j:ℝ)|+1 ≤ (Y:ℝ)) →
      (∀ j ∈ J, witness j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) →

      (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ),
      (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      (∀ j ∈ J, L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
                sourcePhase p.val (witness j)‖) →
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →

      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c den d0 q chiR sigmaR
            M R alpha chiM sigma0 t‖^2) ≤
      3*(3584*(A*(C*K^(Fintype.card ι+Fintype.card β+1)))^2*
         (1+Real.log (4*(Y:ℝ)))^4) := by
  obtain ⟨K,hK,hEvent⟩ :=
    eventually_source_exceptional_physical_sparse_polylog
      a b As Cs q0 vmin tmax
      ha hab hb hAs hCs hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  filter_upwards [hEvent] with L hEL P Y hP hY hPmin hPmax
    hYmin hYmax ι β _ _ _ _
    J witness s hJ hWitness hp hs bs hbs hlarge
    C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi
  let F : ℝ → ℂ := fun t =>
    sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR
      M R alpha chiM sigma0 t

  have hF : Continuous F :=
    sourcePhysicalResidualAt_continuous S Ts Tb q0 Vs
      Vsmall Vbig ts tb coef k G Parity c den d0 q chiR
      sigmaR M R alpha chiM sigma0
  let sample : ℤ → ℝ := sourceUnitMaximizer F hF
  have hSample : ∀ j ∈ J,
      sample j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
    intro j _
    exact sourceUnitMaximizer_mem F hF j
  have hWRange : ∀ j ∈ J, |witness j| ≤ (Y:ℝ) := by
    intro j hj
    exact source_unit_time_range_from_index j (Y:ℝ) (witness j)
      (hJ j hj) (hWitness j hj)
  have hSRange : ∀ j ∈ J, |sample j| ≤ (Y:ℝ) := by
    intro j hj
    exact source_unit_time_range_from_index j (Y:ℝ) (sample j)
      (hJ j hj) (hSample j hj)
  let B : ℝ :=
    3584*(A*(C*K^(Fintype.card ι+Fintype.card β+1)))^2*
      (1+Real.log (4*(Y:ℝ)))^4
  have hClass : ∀ res ∈ Finset.Icc (0:ℤ) 2,
      (∑ i : {j : ℤ // j ∈ J.filter (fun j => j % 3 = res)},
        ‖F (sourceUnitMaximizer F hF i.val)‖^2) ≤ B := by
    intro res hres
    let T : Finset ℤ := J.filter (fun j => j % 3 = res)
    letI : Fintype {j : ℤ // j ∈ T} := Finset.fintypeCoeSort T
    letI : DecidableEq {j : ℤ // j ∈ T} := Classical.decEq _

    have hWT : ∀ i : {j : ℤ // j ∈ T},
        |witness i.val| ≤ (Y:ℝ) := by
      intro i
      exact hWRange i.val (Finset.mem_filter.mp i.property).1
    have hST : ∀ i : {j : ℤ // j ∈ T},
        |sample i.val| ≤ (Y:ℝ) := by
      intro i
      exact hSRange i.val (Finset.mem_filter.mp i.property).1
    have hWSep : ∀ i k : {j : ℤ // j ∈ T},
        i ≠ k → 1 ≤ |witness i.val-witness k.val| :=
      source_mod_three_class_samples_separated J res witness hWitness
    have hSSep : ∀ i k : {j : ℤ // j ∈ T},
        i ≠ k → 1 ≤ |sample i.val-sample k.val| :=
      source_mod_three_class_samples_separated J res sample hSample
    have hLg : ∀ i : {j : ℤ // j ∈ T}, L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
              sourcePhase p.val (witness i.val)‖ := by
      intro i
      exact hlarge i.val (Finset.mem_filter.mp i.property).1
    have hBound := hEL P Y hP hY hPmin hPmax hYmin hYmax
      (fun i : {j : ℤ // j ∈ T} => witness i.val)
      (fun i : {j : ℤ // j ∈ T} => sample i.val)
      s hp hs bs hbs hWT hWSep hST hSSep hLg
      C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc den d0 q chiR sigmaR M R M0 R0
      alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
      hAlpha hChi
    simpa only [F,B,sourcePhysicalResidualAt,sample,T] using hBound
  have hEnergy :=
    source_interval_energy_of_class_subtype_bounds J F hF B hClass
  simpa only [F,B] using hEnergy
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalPhysicalU1Assembly -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.LongPrime

/-! Source-physical exceptional interval energy composed with the
unconditional shifted long-prime U1.  There is no externally supplied
residual-energy hypothesis.  The visible numerical hypotheses record
the original polynomial coefficient and group-size budgets. -/

theorem eventually_source_physical_U1_exceptional_log_saving
    (a b As Cs q0 vmin τ η Cχ : ℝ) (tmax ea ec D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      ∀ (J : Finset ℤ) (witness : ℤ → ℝ) (s : Finset ℕ),
      (∀ j ∈ J, |(j:ℝ)|+1 ≤ (Y:ℝ)) →
      (∀ j ∈ J, witness j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) →
      (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ),
      (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      (∀ j ∈ J, L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
              sourcePhase p.val (witness j)‖) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
      A ≤ L^ea →
      10752*256*(K^(Fintype.card ι+Fintype.card β+1)*Ku)^2 ≤ L →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        L^B₀ + |sigmaL| ≤ |t|) →
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        |t+sigmaL| ≤ x^2) →
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourceCorrelationLongPrime qL chiL N I (t+sigmaL) *
            sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c den d0 q chiR sigmaR
              M R alpha chiM sigma0 t‖^2) ≤ 1/L^D := by
  obtain ⟨K,hK,hPhysical⟩ :=
    eventually_source_exceptional_physical_interval_energy
      a b As Cs q0 vmin tmax
      ha hab hb hAs hCs hq0 hq1 hv
  obtain ⟨B₀,Ku,X₀,hB₀,hKu,hX₀,hLong⟩ :=
    source_shifted_U1_high_frequency_log_saving
      τ η Cχ ea ec D hτ hτη hη hCχ
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hPhysical] with L hEL
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ J witness s hJ hWitness hPrime hS bs hbs hLarge
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax hThreshold
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hLow hHigh
  let F : ℝ → ℂ := fun t =>
    sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR
      M R alpha chiM sigma0 t
  have hF : Continuous F :=
    sourcePhysicalResidualAt_continuous S Ts Tb q0 Vs
      Vsmall Vbig ts tb coef k G Parity c den d0 q chiR
      sigmaR M R alpha chiM sigma0
  have hResidual := hEL P Y hP hY hPmin hPmax hYmin hYmax
    J witness s hJ hWitness hPrime hS bs hbs hLarge
    C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi
  have hR :
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) ≤
      10752*(A*C*K^(Fintype.card ι+Fintype.card β+1))^2*
        (1+Real.log (4*(Y:ℝ)))^4 := by
    convert hResidual using 1 <;> ring
  have hYreal : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hLow' :
      ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        (Real.log x)^B₀ + |sigmaL| ≤ |t| := by
    intro j hj t ht
    simpa only [← hLog] using hLow j hj t ht
  have hFinal := hLong x hx N hNl hNu qL hqL
    (by simpa only [← hLog] using hqLC)
    chiL I hI hISub sigmaL J F hF hLow' hHigh
    L (Y:ℝ) A C (K^(Fintype.card ι+Fintype.card β+1))
    hLog hL3 hYreal hYmax
    hA hAmax hC hCmax (by positivity) hThreshold hR
  simpa only [F] using hFinal
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePhysicalLowFrequency -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! The original low-frequency alpha discrepancy now applies to the
fully marked physical residual coefficient, rather than an arbitrary
bounded Dirichlet coefficient. -/

theorem source_physical_fourfactor_eq_source_residual
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
    (sigmaR : ℝ) (R : Finset ℕ)
    (small long : Finset ℕ) (a b : ℕ)
    (alpha bs bp : ℕ → ℂ)
    {qM : ℕ} (chiM : DirichletCharacter ℂ qM)
    (sigma0 sigma1 t : ℝ) :
    sourceFourFactorAt small long R a b alpha bs bp
      (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR)
      chiM sigma0 sigma1 t =
    (∑ p ∈ small, bs p * (p:ℂ)⁻¹ * sourcePhase p t) *
    (∑ p ∈ long, bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)) *
      sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR
        (Finset.Icc a b) R alpha (fun m => chiM m)
        sigma0 t := by
  rfl

theorem source_physical_low_frequency_fourfactor_energy
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      ∀ (L B x T : ℝ), 0 < L → 0 ≤ T →
      ∀ (alpha : ℕ → ℂ), SourceAlphaDiscrepancy L B x alpha →
      ∀ (qM : ℕ) (chiM : DirichletCharacter ℂ qM),
      ∀ (a b : ℕ), (qM:ℝ) ≤ L^B →
        1 ≤ a → (b:ℝ) ≤ x^2 →
      ∀ (sigma0 sigma1 : ℝ), T+|sigma0| ≤ L^B →
      ∀ (P Pprime R0 : ℕ)
        (small long R : Finset ℕ)
        (bs bp : ℕ → ℂ) (Cs Cl C : ℝ),
      1 ≤ P → 1 ≤ Pprime → 1 ≤ R0 →
      0 ≤ Cs → 0 ≤ Cl → 0 ≤ C →
      small ⊆ Finset.Icc P (2*P) →
      long ⊆ Finset.Icc Pprime (2*Pprime) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ p ∈ small, ‖bs p‖ ≤ Cs) →
      (∀ p ∈ long, ‖bp p‖ ≤ Cl) →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in Set.Icc (-T) T,
        ‖sourceFourFactorAt small long R a b alpha bs bp
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c den d0 q chiR sigmaR)
          chiM sigma0 sigma1 t‖^2) ≤
        2*T*((2*Cs)*(2*Cl)*
          (L^(-B)*(2*(C*K^(Fintype.card ι+Fintype.card β+1)))))^2 := by
  obtain ⟨K,hK,hUniform⟩ :=
    source_physical_marked_residual_uniform_C
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ L B x T hL hT alpha hDisc
    qM chiM a b hqM ha hb sigma0 sigma1 hfreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC hSmall hLong hR hBs hBp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR
  let D : ℝ := C*K^(Fintype.card ι+Fintype.card β+1)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hd (r : ℕ) (_hr : r ∈ R) :
      ‖sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR r‖ ≤ D :=
    hUniform C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc den d0 q chiR sigmaR r
  have hLow := source_fourfactor_low_frequency_integral
    L B x T hL hT alpha hDisc qM chiM a b hqM ha hb
    sigma0 sigma1 hfreq P Pprime R0 small long R
    bs bp
    (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR)
    Cs Cl D hP hPprime hR0 hCs hCl hD hSmall hLong hR
    hBs hBp hd
  simpa only [D] using hLow
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLongPrimePhaseBridge -/

section

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.LongPrime

/-! The *same* shifted long-prime factor in the source U1 and
four-factor Mellin polynomials: cpow equals reciprocal times
the literal real logarithmic source phase. -/

theorem source_prime_cpow_phase_exact (p : ℕ)
    (hp : 0 < p) (t : ℝ) :
    (p:ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) =
      (p:ℂ)⁻¹ * sourcePhase p t := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
  unfold sourcePhase
  rw [Complex.cpow_def_of_ne_zero hp0]
  have hpReal : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hlog : Complex.log (p:ℂ) = ((Real.log (p:ℝ)):ℂ) := by
    simpa using (Complex.ofReal_log hpReal).symm
  rw [hlog]
  congr 1
  push_cast
  ring

noncomputable def sourceLongPrimeSourceSupport (N : ℝ)
    (I : Set ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
    (fun _ => Classical.propDecidable _)
    ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)

/-- Real-source four-factor long polynomial is exactly the
previously certified U1 polynomial, not merely bounded by it. -/
theorem source_long_prime_equals_literal_phase
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (N : ℝ) (I : Set ℝ) (t : ℝ) :
    sourceCorrelationLongPrime q chi N I t =
    ∑ p ∈ sourceLongPrimeSourceSupport N I,
      chi (p:ZMod q) * (p:ℂ)⁻¹ * sourcePhase p t := by
  classical
  unfold sourceCorrelationLongPrime sourceLongPrimeSourceSupport
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime : Nat.Prime p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  rw [source_prime_cpow_phase_exact p hpPrime.pos t]
  ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLongPrimeDyadic -/

section

namespace Green64Analytic.CorrelationMellin

/-! Convert the actual REAL long-prime slot interval I ⊆ [N,2N]
into one NATURAL source dyadic support with P0=ceil N. No support
enlargement is silently assumed; every prime stays in the original I. -/

theorem source_actual_long_prime_nat_dyadic_support
    (N : ℝ) (I : Set ℝ)
    (hI : I ⊆ Set.Icc N (2*N)) :
    sourceLongPrimeSourceSupport N I ⊆
      Finset.Icc ⌈N⌉₊ (2*⌈N⌉₊) := by
  classical
  intro p hp
  have hP : (p : ℝ) ∈ I := by
    simpa only [sourceLongPrimeSourceSupport, Finset.mem_filter] using
      (Finset.mem_filter.mp hp).2
  have hRange := Set.mem_Icc.mp (hI hP)
  have hLower : ⌈N⌉₊ ≤ p := Nat.ceil_le.mpr hRange.1
  have hUpReal : (p:ℝ) ≤ (2*⌈N⌉₊:ℕ) := by
    calc
      _ ≤ 2*N := hRange.2
      _ ≤ 2*⌈N⌉₊ :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil N)
          (by norm_num)
      _ = ((2*⌈N⌉₊:ℕ):ℝ) := by push_cast; ring
  exact Finset.mem_Icc.mpr ⟨hLower, by exact_mod_cast hUpReal⟩

theorem source_actual_long_prime_nat_dyadic_start
    (N : ℝ) (hN : 1 ≤ N) :
    1 ≤ ⌈N⌉₊ := by
  have hCast : (1:ℝ) ≤ ⌈N⌉₊ := hN.trans (Nat.le_ceil N)
  exact_mod_cast hCast

end Green64Analytic.CorrelationMellin

end

/-! ## SourcePhysicalU1GrowingGroups -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.LongPrime

/-! Source-physical exceptional interval energy composed with the
unconditional shifted long-prime U1.  There is no externally supplied
residual-energy hypothesis.  The visible numerical hypotheses record
the original polynomial coefficient and group-size budgets. -/

theorem eventually_source_physical_U1_growing_group_log_saving
    (a b As Cs q0 vmin τ η Cχ C0 : ℝ) (tmax ea ec D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (J : Finset ℤ) (witness : ℤ → ℝ) (s : Finset ℕ),
      (∀ j ∈ J, |(j:ℝ)|+1 ≤ (Y:ℝ)) →
      (∀ j ∈ J, witness j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) →
      (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ),
      (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      (∀ j ∈ J, L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
              sourcePhase p.val (witness j)‖) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
      A ≤ L^ea →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        L^B₀ + |sigmaL| ≤ |t|) →
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        |t+sigmaL| ≤ x^2) →
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourceCorrelationLongPrime qL chiL N I (t+sigmaL) *
            sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c den d0 q chiR sigmaR
              M R alpha chiM sigma0 t‖^2) ≤ 1/L^D := by
  obtain ⟨K,hK,hPhysical⟩ :=
    eventually_source_exceptional_physical_interval_energy
      a b As Cs q0 vmin tmax
      ha hab hb hAs hCs hq0 hq1 hv
  obtain ⟨g,hGroups⟩ :=
    source_literal_group_card_uniform_nat_log_budget K C0 hK hC0
  have hAccuracy : 0 < ((ea+ec+g+D+4:ℕ):ℝ) := by
    exact_mod_cast (by omega : 0 < ea+ec+g+D+4)
  obtain ⟨B₀,Ku,X₀,hB₀,hKu,hX₀,hLong⟩ :=
    source_shifted_U1_high_frequency_interval_energy
      τ η Cχ ((ea+ec+g+D+4:ℕ):ℝ)
      hτ hτη hη hCχ hAccuracy
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hPhysical,
    Filter.eventually_ge_atTop
      (max (max 3 K) (10752*256*Ku^2))] with L hEL hLmin
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ hCardSmall hCardBig J witness s hJ hWitness
    hPrime hS bs hbs hLarge
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hLow hHigh
  let F : ℝ → ℂ := fun t =>
    sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR
      M R alpha chiM sigma0 t
  have hF : Continuous F :=
    sourcePhysicalResidualAt_continuous S Ts Tb q0 Vs
      Vsmall Vbig ts tb coef k G Parity c den d0 q chiR
      sigmaR M R alpha chiM sigma0
  have hResidual := hEL P Y hP hY hPmin hPmax hYmin hYmax
    J witness s hJ hWitness hPrime hS bs hbs hLarge
    C hC S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi
  have hR :
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) ≤
      10752*(A*C*K^(Fintype.card ι+Fintype.card β+1))^2*
        (1+Real.log (4*(Y:ℝ)))^4 := by
    convert hResidual using 1 <;> ring
  have hYreal : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hLow' :
      ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
        (Real.log x)^B₀ + |sigmaL| ≤ |t| := by
    intro j hj t ht
    simpa only [← hLog] using hLow j hj t ht
  have hMarkedBudget :
      K^(Fintype.card ι+Fintype.card β+1) ≤ L^g :=
    hGroups L ((le_max_left _ _).trans hLmin)
      (Fintype.card ι) (Fintype.card β) hCardSmall hCardBig
  have hThreshold : 10752*256*Ku^2 ≤ L :=
    (le_max_right _ _).trans hLmin
  have hLongEnergy := hLong x hx N hNl hNu qL hqL
    (by simpa only [← hLog] using hqLC)
    chiL I hI hISub sigmaL J F hF hLow' hHigh
    (10752*(A*C*K^(Fintype.card ι+Fintype.card β+1))^2*
      (1+Real.log (4*(Y:ℝ)))^4) hR
  rw [← hLog] at hLongEnergy
  simp only [Real.rpow_natCast] at hLongEnergy
  have hNum := source_U1_growing_mark_numeric
    L (Y:ℝ) A C (K^(Fintype.card ι+Fintype.card β+1))
    Ku ea ec g D
    hL3 hYreal hYmax hA hC hAmax hCmax
    (by positivity) hMarkedBudget (le_of_lt hKu) hThreshold
  simpa only [F] using hLongEnergy.trans hNum
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePhysicalHighLowKernelAudit -/

section

/-! Shared Lean 4.34.1 kernel closure for the source-physical high
exceptional, low-frequency discrepancy, exact long-prime phase and
physical collapsed two-factor residual coefficients.  This is not
a theorem asserting full sh:polynomial-target. -/

end

/-! ## SourceActualFrequencyPartition -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

/-! The exceptional indices are extracted from the literal short-prime
Dirichlet polynomial on the actual full Mellin time window. -/

noncomputable def sourceShortPrimeAt
    (s : Finset ℕ) (bs : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p : {p : ℕ // p ∈ s},
    (bs p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val t

theorem sourceShortPrimeAt_continuous (s : Finset ℕ) (bs : ℕ → ℂ) :
    Continuous (sourceShortPrimeAt s bs) := by
  unfold sourceShortPrimeAt
  apply continuous_finset_sum
  intro p hp
  have hpCont : Continuous (fun t : ℝ => sourcePhase p.val t) := by
    simpa only [zero_add] using sourcePhase_continuous p.val 0
  exact hpCont.const_mul _

/-- Finite *actual* occupied integer intervals. No selected set
or preassigned witness times appear in the hypotheses. -/
noncomputable def sourceActualExceptionalUnits
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (⌊-T⌋ - 1 : ℤ) (⌊T⌋ + 1 : ℤ)).filter
    (fun j : ℤ => ∃ t : ℝ,
      t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) ∧
      t ∈ Set.Icc (-T) T ∧
      δ < ‖sourceShortPrimeAt s bs t‖)
theorem sourceActualExceptionalUnits_iff
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ) (j : ℤ) :
    j ∈ sourceActualExceptionalUnits s bs T δ ↔
      j ∈ Finset.Icc (⌊-T⌋ - 1 : ℤ) (⌊T⌋ + 1 : ℤ) ∧
      ∃ t : ℝ, t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) ∧
        t ∈ Set.Icc (-T) T ∧
        δ < ‖sourceShortPrimeAt s bs t‖ := by
  simp only [sourceActualExceptionalUnits, Finset.mem_filter]

noncomputable def sourceActualExceptionalWitness
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ) (j : ℤ) : ℝ :=
  if h : j ∈ sourceActualExceptionalUnits s bs T δ then
    Classical.choose ((sourceActualExceptionalUnits_iff s bs T δ j).mp h).2
  else (j:ℝ)

theorem sourceActualExceptionalWitness_spec
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ)
    (j : ℤ) (hj : j ∈ sourceActualExceptionalUnits s bs T δ) :
    sourceActualExceptionalWitness s bs T δ j ∈
      Set.Icc (j:ℝ) ((j:ℝ)+1) ∧
    sourceActualExceptionalWitness s bs T δ j ∈
      Set.Icc (-T) T ∧
    δ < ‖sourceShortPrimeAt s bs
      (sourceActualExceptionalWitness s bs T δ j)‖ := by
  simp only [sourceActualExceptionalWitness, dif_pos hj]
  exact Classical.choose_spec
    (((sourceActualExceptionalUnits_iff s bs T δ j).mp hj).2)
/-- Every large-value time in the original closed Mellin window
belongs to its canonical occupied unit interval. -/
theorem sourceActualExceptionalUnits_cover
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ t : ℝ)
    (ht : t ∈ Set.Icc (-T) T)
    (hLarge : δ < ‖sourceShortPrimeAt s bs t‖) :
    (⌊t⌋ : ℤ) ∈ sourceActualExceptionalUnits s bs T δ ∧
      t ∈ Set.Ico ((⌊t⌋:ℤ):ℝ) (((⌊t⌋:ℤ):ℝ)+1) := by
  have hLow : (⌊-T⌋ : ℤ) ≤ ⌊t⌋ := Int.floor_mono ht.1
  have hHigh : (⌊t⌋ : ℤ) ≤ ⌊T⌋ := Int.floor_mono ht.2
  have hIco : t ∈
      Set.Ico ((⌊t⌋:ℤ):ℝ) (((⌊t⌋:ℤ):ℝ)+1) :=
    ⟨Int.floor_le t, Int.lt_floor_add_one t⟩
  constructor
  · apply (sourceActualExceptionalUnits_iff s bs T δ _).mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · exact ⟨t, ⟨hIco.1, hIco.2.le⟩, ht, hLarge⟩
  · exact hIco

theorem sourceActualExceptionalUnits_small_outside
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ t : ℝ)
    (ht : t ∈ Set.Icc (-T) T)
    (hOutside : (⌊t⌋ : ℤ) ∉
      sourceActualExceptionalUnits s bs T δ) :
    ‖sourceShortPrimeAt s bs t‖ ≤ δ := by
  exact le_of_not_gt (fun h =>
    hOutside (sourceActualExceptionalUnits_cover s bs T δ t ht h).1)
/-- No two half-open canonical unit cells assign the same time.
Closed cells are used only for integration, where shared endpoints
have Lebesgue measure zero. -/
theorem sourceCanonicalUnitCell_unique
    (j k : ℤ) (t : ℝ)
    (hj : t ∈ Set.Ico (j:ℝ) ((j:ℝ)+1))
    (hk : t ∈ Set.Ico (k:ℝ) ((k:ℝ)+1)) : j = k := by
  by_contra h
  have horder : j+1 ≤ k ∨ k+1 ≤ j := by omega
  rcases horder with hjk | hkj
  · have hh : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hjk
    linarith [hj.2,hk.1]
  · have hh : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hkj
    linarith [hk.2,hj.1]

/-- Source time range condition needed by the verified exceptional
energy theorem, derived from the actual occupied cell witnesses. -/
theorem sourceActualExceptionalUnits_in_Y
    (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ Y : ℝ) (hYT : T+2 ≤ Y)
    (j : ℤ) (hj : j ∈ sourceActualExceptionalUnits s bs T δ) :
    |(j:ℝ)|+1 ≤ Y := by
  obtain ⟨htCell, htWindow, _⟩ :=
    sourceActualExceptionalWitness_spec s bs T δ j hj
  have hBound : |(j:ℝ)| ≤ T+1 := by
    apply abs_le.mpr
    constructor
    · linarith [htCell.2,htWindow.1]
    · linarith [htCell.1,htWindow.2]
  linarith


/-- High-index occupied units, selected from the literal P_s large set. -/
noncomputable def sourceActualHighUnits
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) : Finset ℤ :=
  (sourceActualExceptionalUnits s bs T δ).filter
    (fun j => S+1 ≤ |(j:ℝ)|)

/-- Complementary low-index occupied units. -/
noncomputable def sourceActualLowUnits
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) : Finset ℤ :=
  (sourceActualExceptionalUnits s bs T δ).filter
    (fun j => |(j:ℝ)| < S+1)

theorem sourceActualHighUnits_subset
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    sourceActualHighUnits s bs T δ S ⊆
      sourceActualExceptionalUnits s bs T δ := by
  intro j hj
  exact (Finset.mem_filter.mp hj).1

theorem sourceActualUnits_high_low_partition
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    sourceActualHighUnits s bs T δ S ∪
      sourceActualLowUnits s bs T δ S =
      sourceActualExceptionalUnits s bs T δ := by
  classical
  ext j
  simp only [sourceActualHighUnits, sourceActualLowUnits,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hJ, _⟩ | ⟨hJ, _⟩) <;> exact hJ
  · intro hJ
    rcases lt_or_ge |(j:ℝ)| (S+1) with h | h
    · exact Or.inr ⟨hJ, h⟩
    · exact Or.inl ⟨hJ, h⟩

theorem sourceActualUnits_high_low_disjoint
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    Disjoint (sourceActualHighUnits s bs T δ S)
      (sourceActualLowUnits s bs T δ S) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have hh := (Finset.mem_filter.mp hj).2
  have hl := (Finset.mem_filter.mp hk).2
  linarith

/-- Points in the same closed unit cell differ by at most one.
This gives the exact one-unit high/low buffer. -/
theorem source_unit_abs_le_neighbor
    (j : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    |t| ≤ |(j:ℝ)|+1 ∧ |(j:ℝ)| ≤ |t|+1 := by
  have hdist : |t-(j:ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  have hdist' : |(j:ℝ)-t| ≤ 1 := by
    simpa only [abs_sub_comm] using hdist
  constructor
  · calc
      |t| = |(j:ℝ) + (t-(j:ℝ))| := by ring
      _ ≤ |(j:ℝ)| + |t-(j:ℝ)| := abs_add_le _ _
      _ ≤ |(j:ℝ)| + 1 := by linarith
  · calc
      |(j:ℝ)| = |t + ((j:ℝ)-t)| := by ring
      _ ≤ |t| + |(j:ℝ)-t| := abs_add_le _ _
      _ ≤ |t| + 1 := by linarith

theorem sourceActualHighUnits_frequency
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (j : ℤ) (hj : j ∈ sourceActualHighUnits s bs T δ S)
    (t : ℝ) (ht : t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    S ≤ |t| := by
  have hS : S+1 ≤ |(j:ℝ)| :=
    (Finset.mem_filter.mp hj).2
  have hneighbor := (source_unit_abs_le_neighbor j t ht).2
  linarith

theorem sourceActualLowUnits_frequency
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (j : ℤ) (hj : j ∈ sourceActualLowUnits s bs T δ S)
    (t : ℝ) (ht : t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    |t| < S+2 := by
  have hsmall := (Finset.mem_filter.mp hj).2
  have hneighbor := (source_unit_abs_le_neighbor j t ht).1
  linarith

theorem sourceActualHighUnits_upper_shift
    (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ S Y x sigma : ℝ)
    (hYT : T+2 ≤ Y) (hX : Y+|sigma| ≤ x^2)
    (j : ℤ) (hj : j ∈ sourceActualHighUnits s bs T δ S)
    (t : ℝ) (ht : t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1)) :
    |t+sigma| ≤ x^2 := by
  have hj0 := sourceActualHighUnits_subset s bs T δ S hj
  have hY := sourceActualExceptionalUnits_in_Y
    s bs T δ Y hYT j hj0
  have ht' := (source_unit_abs_le_neighbor j t ht).1
  calc
    |t+sigma| ≤ |t|+|sigma| := abs_add_le _ _
    _ ≤ Y+|sigma| := by linarith
    _ ≤ x^2 := hX

/-- Literal source definition: an integer unit interval belongs to J
if and only if it meets the large-value subset of the full window.
The finite bounding index range is a theorem, not an assumption. -/
theorem sourceActualExceptionalUnits_original_iff
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ) (j : ℤ) :
    j ∈ sourceActualExceptionalUnits s bs T δ ↔
      ∃ t : ℝ, t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) ∧
        t ∈ Set.Icc (-T) T ∧
        δ < ‖sourceShortPrimeAt s bs t‖ := by
  constructor
  · intro hj
    exact ((sourceActualExceptionalUnits_iff s bs T δ j).mp hj).2
  · rintro ⟨t,htCell,htWindow,hLarge⟩
    apply (sourceActualExceptionalUnits_iff s bs T δ j).mpr
    constructor
    · have hl : (⌊-T⌋ : ℤ) ≤ ⌊t⌋ := Int.floor_mono htWindow.1
      have hu : ⌊t⌋ ≤ (⌊T⌋ : ℤ) := Int.floor_mono htWindow.2
      have hjl : j ≤ ⌊t⌋ := (Int.le_floor).mpr htCell.1
      have hju : ⌊t⌋ ≤ j+1 := by
        have hh := Int.floor_mono htCell.2
        simpa using hh
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · exact ⟨t,htCell,htWindow,hLarge⟩

/-- Exact pointwise source high/low/small split on [-T,T].
The two large cases have unique canonical integer index. -/
theorem sourceActualMellinTime_trichotomy
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S t : ℝ)
    (ht : t ∈ Set.Icc (-T) T) :
    ‖sourceShortPrimeAt s bs t‖ ≤ δ ∨
    (δ < ‖sourceShortPrimeAt s bs t‖ ∧
      (⌊t⌋ : ℤ) ∈ sourceActualHighUnits s bs T δ S ∧ S ≤ |t|) ∨
    (δ < ‖sourceShortPrimeAt s bs t‖ ∧
      (⌊t⌋ : ℤ) ∈ sourceActualLowUnits s bs T δ S ∧ |t| < S+2) := by
  by_cases hLarge : δ < ‖sourceShortPrimeAt s bs t‖
  · obtain ⟨hJ,hIco⟩ := sourceActualExceptionalUnits_cover
      s bs T δ t ht hLarge
    have hIcc : t ∈ Set.Icc ((⌊t⌋:ℤ):ℝ) (((⌊t⌋:ℤ):ℝ)+1) :=
      ⟨hIco.1,hIco.2.le⟩
    rcases lt_or_ge |((⌊t⌋:ℤ):ℝ)| (S+1) with hlow | hhigh
    · exact Or.inr (Or.inr ⟨hLarge,
        Finset.mem_filter.mpr ⟨hJ,hlow⟩,
        sourceActualLowUnits_frequency s bs T δ S _
          (Finset.mem_filter.mpr ⟨hJ,hlow⟩) t hIcc⟩)
    · exact Or.inr (Or.inl ⟨hLarge,
        Finset.mem_filter.mpr ⟨hJ,hhigh⟩,
        sourceActualHighUnits_frequency s bs T δ S _
          (Finset.mem_filter.mpr ⟨hJ,hhigh⟩) t hIcc⟩)
  · exact Or.inl (le_of_not_gt hLarge)

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualExceptionalCount -/

section

open Filter
namespace Green64Analytic.CorrelationMellin

/-! Derive the count for genuine source P_s-occupied intervals. -/

theorem eventually_source_actual_exceptional_units_count
    (a b As Cs epsilon : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs) (he : 0 < epsilon) :    ∀ᶠ L : ℝ in atTop,
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ (s : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      ∀ (T : ℝ), T+2 ≤ (Y:ℝ) →
        ((sourceActualExceptionalUnits s bs T (L^(-As))).card:ℝ) ≤
          3*(Y:ℝ)^epsilon := by
  have hCount := eventually_source_exceptional_count_uniform
    a b As Cs epsilon ha hab hb hAs hCs he
  filter_upwards [hCount] with L hL P Y hP hY hPmin hPmax hYmin hYmax
    s bs hp hs hb T hT
  classical
  let J := sourceActualExceptionalUnits s bs T (L^(-As))
  let w := sourceActualExceptionalWitness s bs T (L^(-As))
  have hw : ∀ j ∈ J, w j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
    intro j hj
    exact (sourceActualExceptionalWitness_spec s bs T (L^(-As)) j hj).1
  have hRange : ∀ j ∈ J, |w j| ≤ (Y:ℝ) := by
    intro j hj
    have hwin := (sourceActualExceptionalWitness_spec
      s bs T (L^(-As)) j hj).2.1
    have hw' : |w j| ≤ T := abs_le.mpr hwin
    linarith
  have hClass (res : ℤ) (hr : res ∈ Finset.Icc (0:ℤ) 2) :
      ((J.filter (fun j => j % 3 = res)).card:ℝ) ≤
        (Y:ℝ)^epsilon := by
    let K := J.filter (fun j => j % 3 = res)
    letI : Fintype {j : ℤ // j ∈ K} := Finset.fintypeCoeSort K
    letI : DecidableEq {j : ℤ // j ∈ K} := Classical.decEq _
    have hTimes (i : {j : ℤ // j ∈ K}) :
        |w i.val| ≤ (Y:ℝ) := by
      exact hRange i.val (Finset.mem_filter.mp i.property).1
    have hSep : ∀ i k : {j : ℤ // j ∈ K},
        i ≠ k → 1 ≤ |w i.val-w k.val| :=
      source_mod_three_class_samples_separated J res w hw
    have hLg : ∀ i : {j : ℤ // j ∈ K},
        L^(-As) ≤
          ‖∑ p : {p : ℕ // p ∈ s},
            (bs p.val * ((p.val:ℂ)⁻¹)) *
              sourcePhase p.val (w i.val)‖ := by
      intro i
      have hWitness := (sourceActualExceptionalWitness_spec
        s bs T (L^(-As)) i.val
        (Finset.mem_filter.mp i.property).1).2.2
      exact le_of_lt (by simpa only [sourceShortPrimeAt,w] using hWitness)
    have hBound := hL P Y hP hY hPmin hPmax hYmin hYmax
      (fun i : {j : ℤ // j ∈ K} => w i.val)
      s hp hs bs hb hTimes hSep hLg
    simpa only [K, Fintype.card_coe] using hBound
  have hTotal := source_mod_three_sum_bound J
    (fun _ : ℤ => (1:ℝ)) ((Y:ℝ)^epsilon) (by
      intro res hr
      simpa using hClass res hr)
  simpa [J] using hTotal
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighPhysicalU1 -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.LongPrime

/-! Apply already verified physical high-frequency U1 directly to the
canonical exceptional units of the literal P_s, with no hJ/hWitness
hypothesis and no assumed exceptional-set energy. -/

theorem eventually_source_actual_high_physical_U1
    (a b As Cs q0 vmin τ η Cχ C0 : ℝ) (tmax ea ec D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ), (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      ∀ (T : ℝ), T+2 ≤ (Y:ℝ) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
      A ≤ L^ea →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (Y:ℝ)+|sigmaL| ≤ x^2 →
      (∑ j ∈ sourceActualHighUnits s bs T (L^(-As))
          (L^B₀+|sigmaL|),
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourceCorrelationLongPrime qL chiL N I (t+sigmaL) *
            sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c den d0 q chiR sigmaR
              M R alpha chiM sigma0 t‖^2) ≤ 1/L^D := by
  obtain ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,hHigh⟩ :=
    eventually_source_physical_U1_growing_group_log_saving
      a b As Cs q0 vmin τ η Cχ C0 tmax ea ec D
      ha hab hb hAs hCs hq0 hq1 hv hτ hτη hη hCχ hC0
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hHigh] with L hL
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ hSmall hBig s hp hs bs hbs T hT
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  let J := sourceActualHighUnits s bs T (L^(-As)) (L^B₀+|sigmaL|)
  let w := sourceActualExceptionalWitness s bs T (L^(-As))
  have hJ : ∀ j ∈ J, |(j:ℝ)|+1 ≤ (Y:ℝ) := by
    intro j hj
    exact sourceActualExceptionalUnits_in_Y s bs T (L^(-As))
      (Y:ℝ) hT j (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)
  have hw : ∀ j ∈ J, w j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
    intro j hj
    exact (sourceActualExceptionalWitness_spec s bs T (L^(-As)) j
      (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)).1
  have hLg : ∀ j ∈ J, L^(-As) ≤
      ‖∑ p : {p : ℕ // p ∈ s},
        (bs p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (w j)‖ := by
    intro j hj
    have hLarge := (sourceActualExceptionalWitness_spec s bs T
      (L^(-As)) j
      (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)).2.2
    exact le_of_lt (by simpa only [sourceShortPrimeAt,w] using hLarge)
  have hFreq : ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      L^B₀+|sigmaL| ≤ |t| := by
    intro j hj t ht
    exact sourceActualHighUnits_frequency s bs T (L^(-As))
      (L^B₀+|sigmaL|) j hj t ht
  have hUpper : ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      |t+sigmaL| ≤ x^2 := by
    intro j hj t ht
    exact sourceActualHighUnits_upper_shift s bs T (L^(-As))
      (L^B₀+|sigmaL|) (Y:ℝ) x sigmaL hT hShift j hj t ht
  have hResult := hL x hx hLog hL3 P Y hP hY hPmin hPmax
    hYmin hYmax hSmall hBig J w s hJ hw hp hs bs hbs hLg
    C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax N hNl hNu qL hqL hqLC chiL I
    hI hISub sigmaL hFreq hUpper
  simpa only [J] using hResult
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSmallLargePartition -/

section

namespace Green64Analytic.CorrelationMellin

/-- The literal small-prime polynomial defines a genuine disjoint
partition of the full source Mellin window, including equality at
its threshold (which belongs only to the small part). -/
def sourceActualSmallTimes (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc (-T) T ∧ ‖sourceShortPrimeAt s bs t‖ ≤ δ}

def sourceActualLargeTimes (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc (-T) T ∧ δ < ‖sourceShortPrimeAt s bs t‖}

theorem sourceActualSmallLarge_union (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ : ℝ) :
    sourceActualSmallTimes s bs T δ ∪
      sourceActualLargeTimes s bs T δ = Set.Icc (-T) T := by
  ext t
  simp only [sourceActualSmallTimes, sourceActualLargeTimes,
    Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  · intro ht
    rcases lt_or_ge δ ‖sourceShortPrimeAt s bs t‖ with h | h
    · exact Or.inr ⟨ht, h⟩
    · exact Or.inl ⟨ht, h⟩


theorem sourceActualSmallLarge_disjoint (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ : ℝ) :
    Disjoint (sourceActualSmallTimes s bs T δ)
      (sourceActualLargeTimes s bs T δ) := by
  apply Set.disjoint_left.mpr
  intro t htSmall htLarge
  exact not_lt_of_ge htSmall.2 htLarge.2
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualNonexceptionalFullMeanSquare -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! A finite triple convolution with its exact divisor-fiber mass.
The integral below is over the FULL genuine source small-value set,
not a dyadic sample, a shortened time range or an assumed mean square. -/

noncomputable def sourceThreeCollapsedSupport
    (S : Finset (Fin 3 → ℕ)) : Finset ℕ :=
  S.image (fun v => ∏ i, v i)

noncomputable def sourceThreeCollapsedCoefficient
    (S : Finset (Fin 3 → ℕ))
    (a : Fin 3 → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ v ∈ S.filter (fun v => ∏ i, v i = n),
    ∏ i, a i (v i) / (v i : ℂ)
noncomputable def sourceThreeCollapsedAt
    (S : Finset (Fin 3 → ℕ)) (a : Fin 3 → ℕ → ℂ)
    (t : ℝ) : ℂ :=
  ∑ n ∈ sourceThreeCollapsedSupport S,
    sourceThreeCollapsedCoefficient S a n *
      Complex.exp (((t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I)

theorem sourceThreeCollapsedAt_continuous
    (S : Finset (Fin 3 → ℕ)) (a : Fin 3 → ℕ → ℂ) :
    Continuous (sourceThreeCollapsedAt S a) := by
  unfold sourceThreeCollapsedAt
  fun_prop

theorem source_three_collapsed_true_square_norm
    (N : ℕ) (S : Finset (Fin 3 → ℕ))
    (a : Fin 3 → ℕ → ℂ) (A : Fin 3 → ℝ) (U : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hU : 0 < U)
    (hF : sourceThreeCollapsedSupport S ⊆ Finset.Icc 1 N)
    (hLow : ∀ n ∈ sourceThreeCollapsedSupport S, U ≤ (n:ℝ))
    (ha : ∀ v ∈ S, ∀ i, ‖a i (v i)‖ ≤ A i) :
    (∑ n ∈ sourceThreeCollapsedSupport S,
      ‖sourceThreeCollapsedCoefficient S a n‖^2) ≤
      (∏ i, A i)^2/U * (1+Real.log N)^(2^(2*2)) := by
  exact Green64Analytic.Correlation.collapsedCoefficientMass
    N 2 (sourceThreeCollapsedSupport S) S a A U
    hA hU hF hLow ha

/-- Honest full-range nonexceptional energy. Numeric RHS follows from
the previously kernel-checked continuous Dirichlet mean-value theorem
and the three-factor collapsed divisor-moment theorem. -/
theorem source_actual_nonexceptional_full_mean_square
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ)
    (S : Finset (Fin 3 → ℕ)) (a : Fin 3 → ℕ → ℂ)
    (A : Fin 3 → ℝ) (U : ℝ) (N : ℕ)
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hN : 1 ≤ N)
    (hA : ∀ i, 0 ≤ A i) (hU : 0 < U)
    (hF : sourceThreeCollapsedSupport S ⊆ Finset.Icc 1 N)
    (hLow : ∀ n ∈ sourceThreeCollapsedSupport S, U ≤ (n:ℝ))
    (ha : ∀ v ∈ S, ∀ i, ‖a i (v i)‖ ≤ A i) :
    (∫ t in sourceActualSmallTimes s bs T δ,
      ‖sourceShortPrimeAt s bs t * sourceThreeCollapsedAt S a t‖^2) ≤
    δ^2 * ((2*T + 16*(N:ℝ)*(1+Real.log N)) *
      ((∏ i, A i)^2/U * (1+Real.log N)^(2^(2*2)))) := by
  let G : ℝ → ℂ := sourceThreeCollapsedAt S a
  let E : Set ℝ := sourceActualSmallTimes s bs T δ
  have hG : Continuous G := sourceThreeCollapsedAt_continuous S a
  have hP := sourceShortPrimeAt_continuous s bs
  have hEsub : E ⊆ Set.Icc (-T) T := by
    intro t ht
    exact ht.1
  have hClosed : IsClosed E := by
    change IsClosed (Set.Icc (-T) T ∩
      {t : ℝ | ‖sourceShortPrimeAt s bs t‖ ≤ δ})
    exact isClosed_Icc.inter (isClosed_le hP.norm continuous_const)
  have hMeas : MeasurableSet E := hClosed.measurableSet
  have hGInt : IntegrableOn (fun t : ℝ => ‖G t‖^2)
      (Set.Icc (-T) T) :=
    (hG.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hEGInt : IntegrableOn (fun t : ℝ => ‖G t‖^2) E :=
    hGInt.mono_set hEsub
  have hFG : Continuous (fun t : ℝ => sourceShortPrimeAt s bs t * G t) :=
    hP.mul hG
  have hFGInt : IntegrableOn
      (fun t : ℝ => ‖sourceShortPrimeAt s bs t * G t‖^2) E :=
    ((hFG.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hEsub
  have hPoint (t : ℝ) (ht : t ∈ E) :
      ‖sourceShortPrimeAt s bs t * G t‖^2 ≤ δ^2 * ‖G t‖^2 := by
    have hs : ‖sourceShortPrimeAt s bs t‖ ≤ δ := ht.2
    have hSq := (sq_le_sq₀ (norm_nonneg _) hδ).mpr hs
    calc
      _ = ‖sourceShortPrimeAt s bs t‖^2 * ‖G t‖^2 := by rw [norm_mul]; ring
      _ ≤ δ^2 * ‖G t‖^2 :=
        mul_le_mul_of_nonneg_right hSq (sq_nonneg _)
  have hEControl :
      (∫ t in E, ‖sourceShortPrimeAt s bs t * G t‖^2) ≤
        δ^2 * (∫ t in E, ‖G t‖^2) := by
    have hDInt : IntegrableOn (fun t : ℝ => δ^2 * ‖G t‖^2) E :=
      hEGInt.const_mul _
    calc
      _ ≤ ∫ t in E, δ^2 * ‖G t‖^2 :=
        setIntegral_mono_on hFGInt hDInt hMeas hPoint
      _ = δ^2 * (∫ t in E, ‖G t‖^2) := by
        rw [integral_const_mul]
  have hEMono : (∫ t in E, ‖G t‖^2) ≤
      (∫ t in Set.Icc (-T) T, ‖G t‖^2) := by
    apply setIntegral_mono_set hGInt
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (‖G t‖))
    · exact hEsub.eventuallySubset
  have hMV0 := Green64Analytic.Correlation.continuousMeanSquare
    N (sourceThreeCollapsedSupport S)
    (sourceThreeCollapsedCoefficient S a) (-T) T hF (by linarith)
  have hMV : (∫ t in Set.Icc (-T) T, ‖G t‖^2) ≤
      (2*T+16*(N:ℝ)*(1+Real.log N)) *
        (∑ n ∈ sourceThreeCollapsedSupport S,
          ‖sourceThreeCollapsedCoefficient S a n‖^2) := by
    convert hMV0 using 1
    · rfl
    · ring
  have hMass := source_three_collapsed_true_square_norm
    N S a A U hA hU hF hLow ha
  have hLogN : 0 ≤ Real.log (N:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hBnonneg : 0 ≤ 2*T+16*(N:ℝ)*(1+Real.log N) := by
    positivity
  change (∫ t in E, ‖sourceShortPrimeAt s bs t * G t‖^2) ≤
    δ^2 * ((2*T+16*(N:ℝ)*(1+Real.log N)) *
      ((∏ i, A i)^2/U * (1+Real.log N)^(2^(2*2))))
  calc
    _ ≤ δ^2 * (∫ t in E, ‖G t‖^2) := hEControl
    _ ≤ δ^2 * (∫ t in Set.Icc (-T) T, ‖G t‖^2) :=
      mul_le_mul_of_nonneg_left hEMono (sq_nonneg δ)
    _ ≤ δ^2 * ((2*T+16*(N:ℝ)*(1+Real.log N)) *
        (∑ n ∈ sourceThreeCollapsedSupport S,
          ‖sourceThreeCollapsedCoefficient S a n‖^2)) :=
      mul_le_mul_of_nonneg_left hMV (sq_nonneg δ)
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hMass hBnonneg) (sq_nonneg δ)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualIntegralSplit -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

/-! Exact Lebesgue integral partition of the *original full*
source Mellin window by the literal short-prime polynomial.
No exceptional-set parameter or covering hypothesis is introduced. -/

theorem source_actual_mellin_integral_split
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in Set.Icc (-T) T, ‖F t‖^2) =
      (∫ t in sourceActualSmallTimes s bs T δ, ‖F t‖^2) +
      (∫ t in sourceActualLargeTimes s bs T δ, ‖F t‖^2) := by
  have hP : Continuous (sourceShortPrimeAt s bs) :=
    sourceShortPrimeAt_continuous s bs
  have hSmall : MeasurableSet (sourceActualSmallTimes s bs T δ) := by
    change MeasurableSet (Set.Icc (-T) T ∩
      {t : ℝ | ‖sourceShortPrimeAt s bs t‖ ≤ δ})
    exact isClosed_Icc.measurableSet.inter
      (isClosed_le hP.norm continuous_const).measurableSet
  have hLarge : MeasurableSet (sourceActualLargeTimes s bs T δ) := by
    change MeasurableSet (Set.Icc (-T) T ∩
      {t : ℝ | δ < ‖sourceShortPrimeAt s bs t‖})
    exact isClosed_Icc.measurableSet.inter
      (isOpen_lt continuous_const hP.norm).measurableSet
  have hInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (Set.Icc (-T) T) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hSmallInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (sourceActualSmallTimes s bs T δ) :=
    hInt.mono_set (fun _ ht => ht.1)
  have hLargeInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (sourceActualLargeTimes s bs T δ) :=
    hInt.mono_set (fun _ ht => ht.1)
  calc
    _ = ∫ t in sourceActualSmallTimes s bs T δ ∪
          sourceActualLargeTimes s bs T δ, ‖F t‖^2 := by
            rw [sourceActualSmallLarge_union]
    _ = _ := setIntegral_union
      (sourceActualSmallLarge_disjoint s bs T δ)
      hLarge hSmallInt hLargeInt

/-- In particular, the product of the *same* literal small-prime
polynomial and the actual three-factor collapsed convolution splits
with no boundary mass and no loss from threshold equality. -/
theorem source_actual_triple_mellin_integral_split
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ)
    (S : Finset (Fin 3 → ℕ)) (a : Fin 3 → ℕ → ℂ) :
    (∫ t in Set.Icc (-T) T,
      ‖sourceShortPrimeAt s bs t * sourceThreeCollapsedAt S a t‖^2) =
    (∫ t in sourceActualSmallTimes s bs T δ,
      ‖sourceShortPrimeAt s bs t * sourceThreeCollapsedAt S a t‖^2) +
    (∫ t in sourceActualLargeTimes s bs T δ,
      ‖sourceShortPrimeAt s bs t * sourceThreeCollapsedAt S a t‖^2) := by
  exact source_actual_mellin_integral_split s bs T δ
    (fun t => sourceShortPrimeAt s bs t *
      sourceThreeCollapsedAt S a t)
    ((sourceShortPrimeAt_continuous s bs).mul
      (sourceThreeCollapsedAt_continuous S a))

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLargeUnitEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! A genuinely disjoint half-open unit-cell decomposition of a
measurable set, and an upper bound by closed unit-cell energies.
This is the integration bridge from actual prime-large time sets
to the already certified high-frequency U1 theorem. -/

def sourceHalfOpenUnit (j : ℤ) : Set ℝ :=
  Set.Ico (j:ℝ) ((j:ℝ)+1)

def sourceClosedUnit (j : ℤ) : Set ℝ :=
  Set.Icc (j:ℝ) ((j:ℝ)+1)

theorem source_half_open_unit_disjoint
    (j k : ℤ) (hjk : j ≠ k) :
    Disjoint (sourceHalfOpenUnit j) (sourceHalfOpenUnit k) := by
  apply Set.disjoint_left.mpr
  intro t hj hk
  exact hjk (sourceCanonicalUnitCell_unique j k t hj hk)

theorem source_half_open_covered_integral_bound
    (J : Finset ℤ) (E : Set ℝ) (hE : MeasurableSet E)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in ⋃ j ∈ J, E ∩ sourceHalfOpenUnit j, ‖F t‖^2) ≤
      ∑ j ∈ J, ∫ t in sourceClosedUnit j, ‖F t‖^2 := by
  classical
  let f : ℝ → ℝ := fun t => ‖F t‖^2
  have hMeas (j : ℤ) (hj : j ∈ J) :
      MeasurableSet (E ∩ sourceHalfOpenUnit j) :=
    hE.inter measurableSet_Ico
  have hDisj : Set.Pairwise (↑J : Set ℤ)
      (fun j k => Disjoint (E ∩ sourceHalfOpenUnit j)
        (E ∩ sourceHalfOpenUnit k)) := by
    intro j hj k hk hne
    apply Set.disjoint_left.mpr
    intro t htj htk
    exact hne (sourceCanonicalUnitCell_unique j k t htj.2 htk.2)
  have hClosedInt (j : ℤ) :
      IntegrableOn f (sourceClosedUnit j) := by
    exact (hF.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc)
  have hClipInt (j : ℤ) (hj : j ∈ J) :
      IntegrableOn f (E ∩ sourceHalfOpenUnit j) := by
    apply (hClosedInt j).mono_set
    intro t ht
    exact ⟨ht.2.1, ht.2.2.le⟩
  have hClipLe (j : ℤ) (hj : j ∈ J) :
      (∫ t in E ∩ sourceHalfOpenUnit j, ‖F t‖^2) ≤
        ∫ t in sourceClosedUnit j, ‖F t‖^2 := by
    apply setIntegral_mono_set (hClosedInt j)
    · exact Filter.Eventually.of_forall
        (fun t => sq_nonneg (‖F t‖))
    · have hSub : E ∩ sourceHalfOpenUnit j ⊆ sourceClosedUnit j := by
        intro t ht
        exact ⟨ht.2.1, ht.2.2.le⟩
      exact hSub.eventuallySubset
  calc
    _ = ∑ j ∈ J, ∫ t in E ∩ sourceHalfOpenUnit j, ‖F t‖^2 := by
      exact integral_biUnion_finset J hMeas hDisj hClipInt
    _ ≤ _ := Finset.sum_le_sum hClipLe

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighLowLargePartition -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Literal large-P_s time set split into high/low occupied cells.
The decomposition uses canonical half-open integer cells. -/

def sourceActualLargeHighTimes
    (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ S : ℝ) : Set ℝ :=
  ⋃ j ∈ sourceActualHighUnits s bs T δ S,
    sourceActualLargeTimes s bs T δ ∩ sourceHalfOpenUnit j

def sourceActualLargeLowTimes
    (s : Finset ℕ) (bs : ℕ → ℂ)
    (T δ S : ℝ) : Set ℝ :=
  ⋃ j ∈ sourceActualLowUnits s bs T δ S,
    sourceActualLargeTimes s bs T δ ∩ sourceHalfOpenUnit j

theorem source_actual_large_high_low_union
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    sourceActualLargeHighTimes s bs T δ S ∪
      sourceActualLargeLowTimes s bs T δ S =
        sourceActualLargeTimes s bs T δ := by
  classical
  ext t
  simp only [sourceActualLargeHighTimes, sourceActualLargeLowTimes,
    Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro (⟨j, hj, ht, hc⟩ | ⟨j, hj, ht, hc⟩) <;> exact ht
  · intro ht
    obtain ⟨hJ, hCell⟩ := sourceActualExceptionalUnits_cover
      s bs T δ t ht.1 ht.2
    rcases lt_or_ge |((⌊t⌋:ℤ):ℝ)| (S+1) with hlo | hhi
    · right
      exact ⟨⌊t⌋, Finset.mem_filter.mpr ⟨hJ,hlo⟩,ht,hCell⟩
    · left
      exact ⟨⌊t⌋, Finset.mem_filter.mpr ⟨hJ,hhi⟩,ht,hCell⟩
theorem source_actual_large_high_low_disjoint
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    Disjoint (sourceActualLargeHighTimes s bs T δ S)
      (sourceActualLargeLowTimes s bs T δ S) := by
  classical
  apply Set.disjoint_left.mpr
  intro t htH htL
  rcases Set.mem_iUnion.mp htH with ⟨j,hj'⟩
  rcases Set.mem_iUnion.mp hj' with ⟨hj,⟨_,hcellJ⟩⟩
  rcases Set.mem_iUnion.mp htL with ⟨k,hk'⟩
  rcases Set.mem_iUnion.mp hk' with ⟨hk,⟨_,hcellK⟩⟩
  have heq : j = k :=
    sourceCanonicalUnitCell_unique j k t hcellJ hcellK
  have hDisj := sourceActualUnits_high_low_disjoint s bs T δ S
  exact (Finset.disjoint_left.mp hDisj) hj (heq ▸ hk)

theorem source_actual_large_measurable
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ : ℝ) :
    MeasurableSet (sourceActualLargeTimes s bs T δ) := by
  change MeasurableSet (Set.Icc (-T) T ∩
    {t : ℝ | δ < ‖sourceShortPrimeAt s bs t‖})
  exact isClosed_Icc.measurableSet.inter
    (isOpen_lt continuous_const
      (sourceShortPrimeAt_continuous s bs).norm).measurableSet

theorem source_actual_large_high_measurable
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    MeasurableSet (sourceActualLargeHighTimes s bs T δ S) := by
  change MeasurableSet (⋃ j ∈ sourceActualHighUnits s bs T δ S,
    sourceActualLargeTimes s bs T δ ∩ sourceHalfOpenUnit j)
  exact Finset.measurableSet_biUnion _
    (fun j hj => (source_actual_large_measurable s bs T δ).inter
      measurableSet_Ico)

theorem source_actual_large_low_measurable
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    MeasurableSet (sourceActualLargeLowTimes s bs T δ S) := by
  change MeasurableSet (⋃ j ∈ sourceActualLowUnits s bs T δ S,
    sourceActualLargeTimes s bs T δ ∩ sourceHalfOpenUnit j)
  exact Finset.measurableSet_biUnion _
    (fun j hj => (source_actual_large_measurable s bs T δ).inter
      measurableSet_Ico)
theorem source_actual_large_high_energy_cover
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in sourceActualLargeHighTimes s bs T δ S,
      ‖F t‖^2) ≤
    ∑ j ∈ sourceActualHighUnits s bs T δ S,
      ∫ t in sourceClosedUnit j, ‖F t‖^2 := by
  exact source_half_open_covered_integral_bound
    (sourceActualHighUnits s bs T δ S)
    (sourceActualLargeTimes s bs T δ)
    (source_actual_large_measurable s bs T δ) F hF

theorem source_actual_large_low_energy_cover
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in sourceActualLargeLowTimes s bs T δ S,
      ‖F t‖^2) ≤
    ∑ j ∈ sourceActualLowUnits s bs T δ S,
      ∫ t in sourceClosedUnit j, ‖F t‖^2 := by
  exact source_half_open_covered_integral_bound
    (sourceActualLowUnits s bs T δ S)
    (sourceActualLargeTimes s bs T δ)
    (source_actual_large_measurable s bs T δ) F hF
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFullFrequencyIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Exact FULL source Mellin frequency split at the integral level.
All large-time sets are the occupied cells of the LITERAL P_s(t).
The low/high unit classes are disjoint, so no endpoint mass occurs. -/

theorem source_actual_large_high_low_integral_split
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in sourceActualLargeTimes s bs T δ, ‖F t‖^2) =
      (∫ t in sourceActualLargeHighTimes s bs T δ S, ‖F t‖^2) +
      (∫ t in sourceActualLargeLowTimes s bs T δ S, ‖F t‖^2) := by
  have hIccInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (Set.Icc (-T) T) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hHighSub :
      sourceActualLargeHighTimes s bs T δ S ⊆ Set.Icc (-T) T := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨j,hj'⟩
    rcases Set.mem_iUnion.mp hj' with ⟨_, htCell⟩
    exact htCell.1.1
  have hLowSub :
      sourceActualLargeLowTimes s bs T δ S ⊆ Set.Icc (-T) T := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨j,hj'⟩
    rcases Set.mem_iUnion.mp hj' with ⟨_, htCell⟩
    exact htCell.1.1
  have hHighInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (sourceActualLargeHighTimes s bs T δ S) :=
    hIccInt.mono_set hHighSub
  have hLowInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (sourceActualLargeLowTimes s bs T δ S) :=
    hIccInt.mono_set hLowSub
  calc
    _ = ∫ t in sourceActualLargeHighTimes s bs T δ S ∪
        sourceActualLargeLowTimes s bs T δ S, ‖F t‖^2 := by
      rw [source_actual_large_high_low_union]
    _ = _ := setIntegral_union
      (source_actual_large_high_low_disjoint s bs T δ S)
      (source_actual_large_low_measurable s bs T δ S)
      hHighInt hLowInt

theorem source_actual_full_mellin_three_way_integral
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in Set.Icc (-T) T, ‖F t‖^2) =
      (∫ t in sourceActualSmallTimes s bs T δ, ‖F t‖^2) +
      (∫ t in sourceActualLargeHighTimes s bs T δ S, ‖F t‖^2) +
      (∫ t in sourceActualLargeLowTimes s bs T δ S, ‖F t‖^2) := by
  rw [source_actual_mellin_integral_split s bs T δ F hF,
    source_actual_large_high_low_integral_split s bs T δ S F hF]
  ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLowFrequencyIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Exact low-frequency localization of the occupied large-prime
Mellin range. The one-unit endpoint buffer is inherited from
sourceActualLowUnits_frequency, not an auxiliary assumption on J. -/

theorem source_actual_large_low_frequency_subset
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ) :
    sourceActualLargeLowTimes s bs T δ S ⊆
      Set.Icc (-(S+2)) (S+2) := by
  intro t ht
  rcases Set.mem_iUnion.mp ht with ⟨j,hj'⟩
  rcases Set.mem_iUnion.mp hj' with ⟨hj,⟨_,hcell⟩⟩
  have hBound := sourceActualLowUnits_frequency s bs T δ S
    j hj t ⟨hcell.1, hcell.2.le⟩
  exact abs_le.mp hBound.le

theorem source_actual_large_low_energy_from_full_interval
    (s : Finset ℕ) (bs : ℕ → ℂ) (T δ S : ℝ)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in sourceActualLargeLowTimes s bs T δ S,
      ‖F t‖^2) ≤
        ∫ t in Set.Icc (-(S+2)) (S+2), ‖F t‖^2 := by
  have hInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (Set.Icc (-(S+2)) (S+2)) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  apply setIntegral_mono_set hInt
  · exact Filter.Eventually.of_forall
      (fun t => sq_nonneg (‖F t‖))
  · exact (source_actual_large_low_frequency_subset s bs T δ S).eventuallySubset
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualTripleCollapse -/

section

namespace Green64Analytic.CorrelationMellin

/-! Exact three-factor source collapse, retaining every coefficient,
fixed source shift and multiplicity of the original product. -/

def sourceThreeTuple (m p r : ℕ) : Fin 3 → ℕ :=
  fun i => if i = 0 then m else if i = 1 then p else r

@[simp] theorem sourceThreeTuple_zero (m p r : ℕ) :
    sourceThreeTuple m p r 0 = m := by simp [sourceThreeTuple]
@[simp] theorem sourceThreeTuple_one (m p r : ℕ) :
    sourceThreeTuple m p r 1 = p := by simp [sourceThreeTuple]
@[simp] theorem sourceThreeTuple_two (m p r : ℕ) :
    sourceThreeTuple m p r 2 = r := by simp [sourceThreeTuple]

noncomputable def sourceThreeActualTuples
    (M P R : Finset ℕ) : Finset (Fin 3 → ℕ) :=
  ((M.product P).product R).image
    (fun z => sourceThreeTuple z.1.1 z.1.2 z.2)
theorem sourceThreeTuple_injective : Function.Injective
    (fun z : (ℕ × ℕ) × ℕ => sourceThreeTuple z.1.1 z.1.2 z.2) := by
  intro z w h
  rcases z with ⟨⟨m,p⟩,r⟩
  rcases w with ⟨⟨m',p'⟩,r'⟩
  have hm : m = m' := by
    simpa using congrArg (fun f : Fin 3 → ℕ => f 0) h
  have hp : p = p' := by
    simpa using congrArg (fun f : Fin 3 → ℕ => f 1) h
  have hr : r = r' := by
    simpa using congrArg (fun f : Fin 3 → ℕ => f 2) h
  simp [hm,hp,hr]

theorem sourceThreeTuple_product (m p r : ℕ) :
    (∏ i, sourceThreeTuple m p r i) = m*p*r := by
  simp [Fin.prod_univ_three]
/-- Fibre collapsing does not omit or double-count any multiplicity. -/
theorem source_three_collapsed_sum_identity
    (S : Finset (Fin 3 → ℕ)) (a : Fin 3 → ℕ → ℂ) (t : ℝ) :
    sourceThreeCollapsedAt S a t =
      ∑ v ∈ S, (∏ i, a i (v i) / (v i : ℂ)) *
        Complex.exp (((t*Real.log ((∏ i, v i):ℝ):ℝ):ℂ)*Complex.I) := by
  classical
  simp only [sourceThreeCollapsedAt, sourceThreeCollapsedCoefficient,
    sourceThreeCollapsedSupport, Finset.sum_mul, Finset.sum_filter,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.sum_ite_eq]
  have hvImage : (∏ i, v i) ∈
      S.image (fun x => ∏ i, x i) :=
    Finset.mem_image.mpr ⟨v,hv,rfl⟩
  rw [if_pos hvImage]
  simp only [Nat.cast_prod]

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualThreeFactorProduct -/

section

namespace Green64Analytic.CorrelationMellin

/-! No auxiliary convolution coefficient is assumed: every source
three-factor tuple and its multiplicity are preserved. -/

noncomputable def sourceThreeProductCoefficients
    (am ap ar : ℕ → ℂ) : Fin 3 → ℕ → ℂ :=
  fun i n => if i = 0 then am n else if i = 1 then ap n else ar n

theorem source_three_actual_product_identity
    (M P R : Finset ℕ) (am ap ar : ℕ → ℂ) (t : ℝ)
    (hM : ∀ m ∈ M, 0 < m) (hP : ∀ p ∈ P, 0 < p)
    (hR : ∀ r ∈ R, 0 < r) :
    sourceThreeCollapsedAt (sourceThreeActualTuples M P R)
      (sourceThreeProductCoefficients am ap ar) t =
    (∑ m ∈ M, (am m / (m : ℂ)) * sourcePhase m t) *
    (∑ p ∈ P, (ap p / (p : ℂ)) * sourcePhase p t) *
    (∑ r ∈ R, (ar r / (r : ℂ)) * sourcePhase r t) := by
  classical
  rw [source_three_collapsed_sum_identity]
  let E := (M.product P).product R
  let f : ((ℕ × ℕ) × ℕ) → (Fin 3 → ℕ) :=
    fun z => sourceThreeTuple z.1.1 z.1.2 z.2
  have hInj : Set.InjOn f (↑E : Set ((ℕ × ℕ) × ℕ)) := by
    intro u hu v hv huv
    exact sourceThreeTuple_injective huv
  change (∑ v ∈ E.image f,
    (∏ i, sourceThreeProductCoefficients am ap ar i (v i) / (v i : ℂ)) *
      Complex.exp (((t*Real.log ((∏ i, v i):ℝ):ℝ):ℂ)*Complex.I)) = _
  rw [Finset.sum_image hInj]
  have hTerm (m p r : ℕ)
      (hm : 0 < m) (hp : 0 < p) (hr : 0 < r) :
      (∏ i, sourceThreeProductCoefficients am ap ar i
        (sourceThreeTuple m p r i) / (sourceThreeTuple m p r i : ℂ)) *
        Complex.exp (((t*Real.log ((∏ i, sourceThreeTuple m p r i):ℝ):ℝ):ℂ)*Complex.I) =
      ((am m / (m:ℂ)) * sourcePhase m t) *
      ((ap p / (p:ℂ)) * sourcePhase p t) *
      ((ar r / (r:ℂ)) * sourcePhase r t) := by
    have hProd : (∏ i, sourceThreeProductCoefficients am ap ar i
        (sourceThreeTuple m p r i) / (sourceThreeTuple m p r i : ℂ)) =
        (am m / (m:ℂ)) * (ap p / (p:ℂ)) * (ar r / (r:ℂ)) := by
      simp [Fin.prod_univ_three, sourceThreeTuple,
        sourceThreeProductCoefficients, div_eq_mul_inv, mul_inv_rev]
      all_goals ring
    have hPhase :
      Complex.exp (((t*Real.log ((∏ i, sourceThreeTuple m p r i):ℝ):ℝ):ℂ)*Complex.I) =
      sourcePhase m t * sourcePhase p t * sourcePhase r t := by
      have hCastProd : (∏ i, (sourceThreeTuple m p r i : ℝ)) =
          ((m*p*r:ℕ):ℝ) := by
        simp only [← Nat.cast_prod, sourceThreeTuple_product]
      rw [hCastProd]
      have hh : Complex.exp (((t*Real.log ((m*p*r:ℕ):ℝ):ℝ):ℂ)*Complex.I) =
          sourcePhase (m*p*r) t := by
        unfold sourcePhase
        congr 1
        ring
      rw [hh, sourcePhase_mul (m*p) r (Nat.mul_pos hm hp) hr t,
        sourcePhase_mul m p hm hp t]
    rw [hProd,hPhase]
    ring
  have hTriple :
      (∑ z ∈ E,
        (∏ i, sourceThreeProductCoefficients am ap ar i (f z i) / (f z i : ℂ)) *
          Complex.exp (((t*Real.log ((∏ i, f z i):ℝ):ℝ):ℂ)*Complex.I)) =
      ∑ m ∈ M, ∑ p ∈ P, ∑ r ∈ R,
        ((am m / (m:ℂ)) * sourcePhase m t) *
        ((ap p / (p:ℂ)) * sourcePhase p t) *
        ((ar r / (r:ℂ)) * sourcePhase r t) := by
    let g : ((ℕ × ℕ) × ℕ) → ℂ := fun z =>
      (∏ i, sourceThreeProductCoefficients am ap ar i (f z i) / (f z i : ℂ)) *
        Complex.exp (((t*Real.log ((∏ i, f z i):ℝ):ℝ):ℂ)*Complex.I)
    change (∑ z ∈ E, g z) = _
    calc
      _ = ∑ z ∈ E, g (z.1,z.2) := by
        apply Finset.sum_congr rfl
        intro z hz
        cases z
        rfl
      _ = ∑ mp ∈ M.product P, ∑ r ∈ R, g (mp,r) := by
        exact Finset.sum_product' (M.product P) R (fun mp r => g (mp,r))
      _ = ∑ mp ∈ M.product P, ∑ r ∈ R, g ((mp.1,mp.2),r) := by
        apply Finset.sum_congr rfl
        intro mp hmp
        cases mp
        rfl
      _ = ∑ m ∈ M, ∑ p ∈ P, ∑ r ∈ R, g ((m,p),r) := by
        exact Finset.sum_product' M P
          (fun m p => ∑ r ∈ R, g ((m,p),r))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro r hr
        exact hTerm m p r (hM m hm) (hP p hp) (hR r hr)
  rw [hTriple]
  calc
    _ = (∑ m ∈ M, ∑ p ∈ P,
          ((am m / (m:ℂ)) * sourcePhase m t) *
          ((ap p / (p:ℂ)) * sourcePhase p t)) *
        (∑ r ∈ R, ((ar r / (r:ℂ)) * sourcePhase r t)) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [← Finset.sum_mul_sum]

end Green64Analytic.CorrelationMellin

end

