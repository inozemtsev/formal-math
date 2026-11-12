module

public import Green64.Library.Weights.Part040
public import Green64.Library.Weights.Part033
public import Green64.Library.Weights.Part021
public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part039
public import Green64.Library.Analysis.Estimates.Part006
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part012
public import Mathlib

@[expose] public section

/-!
# Weights / Part041

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceActualUniformFullLogInput -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Green64Analytic.CorrelationMellin
/- Terminal full original window with the ORIGINAL logarithmic psi1(exp u)
derivative budget. Normalizing by w/Y incurs only fixed constants.
The cutoff family is quantified after L; no Fourier energy/tail is assumed. -/
theorem eventually_source_actual_uniform_full_window_original_log_budget
    (aexp bexp τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) 
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base (max vexp fcut+2) + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      2*L*(16*A)*(P:ℝ)*L^Carc ≤ Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2*(epsi+1)+2+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      ∀ (psi1 : ℝ → ℂ)
        (hSmooth : ContDiff ℝ ∞ psi1)
        (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
        (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceActualOriginalWindowWeight Y psi1 v1)
          (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤
      (L^D)⁻¹ := by
  let Knew := sourceNormalizedLogDerivativeConstants A Kpsi
  have hKnew : ∀ j, 0 ≤ Knew j := source_normalized_log_derivative_constants_nonneg
    A Kpsi (by linarith) hKpsi
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_uniform_full_window_all_boxes
      aexp bexp τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Knew
      hA hCpsi hKnew hepsi hFcut
      haexp hab hb hτ hτη hη hCχ hC0 hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hFree hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups
  intro lo hi a b alpha ha hbAlpha hM hAlpha hDisc
  intro small R bs hSmallPrime hSmall hBs hR
  intro qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
  intro sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR psi1 hSmooth hSupport v1 hv1 hBudget
  have hBudgetNew := source_actual_normalized_log_derivative_budget
    A Cpsi L Kpsi psi1 hA hCpsi hKpsi (by linarith) hSmooth hSupport hBudget
  exact hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI hNlow hNhigh hPmin hPmax
    hFree hYstrong hSmallGroups hBigGroups
    lo hi a b alpha ha hbAlpha hM hAlpha hDisc
    small R bs hSmallPrime hSmall hBs hR
    qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
    sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
    S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR psi1 hSmooth hSupport v1 hv1 hBudgetNew
end Green64Analytic.CorrelationMellin

end

/-! ## SourcePeelingResidualArc -/

section

open scoped BigOperators
open MeasureTheory

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The original physical marked peeling *difference* has a finite
Fourier polynomial with the true n_* core and the parity twist. -/
noncomputable def sourcePeelingResidualFourier
    (allGroupPrimes S primeSlot Ptwist : Finset ℕ)
    (W_hi W_lo : ℕ → ℂ) (V : ℝ)
    (α c : ℕ → ℂ) (N q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    C(AddCircle (1:ℝ), ℂ) :=
  sourceNatFourierPoly (sourceSquareExceptionalSupport N S)
    (fun n => literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (sourcePeelingError S V W_hi W_lo)
        primeSlot α c q χ σ₀ σ₁ n)

/-- Exact source p²-peeling-difference Fourier major-arc energy.
Only the two *explicit source marked-weight caps* remain; no
Fourier energy, divisor-moment or square L² estimate is assumed. -/
theorem source_physical_peeling_residual_beta_arc
    (allGroupPrimes S primeSlot Ptwist : Finset ℕ)
    (W_hi W_lo : ℕ → ℂ) (V : ℝ)
    (α c : ℕ → ℂ) (N P q : ℕ)
    (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ A C B vmin L a D center H : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hα : ∀ m, ‖α m‖ ≤ A) (hc : ∀ r, ‖c r‖ ≤ C)
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hS : S ⊆ Finset.Icc P (2*P))
    (hGroups : S ⊆ allGroupPrimes)
    (hPrime : ∀ p ∈ S, p.Prime)
    (hLow : Real.exp (L^a)/2 ≤ (P:ℝ))
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hv : 0 < vmin) (hV : vmin ≤ V)
    (hlogN : Real.log (N:ℝ) ≤ D*L)
    (hhi : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ‖W_hi n‖ ≤ B)
    (hlo : ∀ n ∈ sourceSquareExceptionalSupport N S,
       ∀ p ∈ smallPrimeSupport S n,
         ‖W_lo (n/p)‖ ≤ B)
    (hH : 2 ≤ H) :
    (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
       ‖sourcePeelingResidualFourier
         allGroupPrimes S primeSlot Ptwist W_hi W_lo V
         α c N q χ σ₀ σ₁
          ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
      4*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
        (N:ℝ)*(1+Real.log (N:ℝ))^16*
          Real.exp (-(L^a)) := by
  have hF := source_beta_window_fourier_energy_le_coeff_l2
    (sourceSquareExceptionalSupport N S)
    (fun n => literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (sourcePeelingError S V W_hi W_lo)
        primeSlot α c q χ σ₀ σ₁ n)
    center H hH
  have hcount : (∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖literalSourceParity Ptwist n *
         sourceEndpoint (sourceOutsidePart allGroupPrimes)
           (sourcePeelingError S V W_hi W_lo)
           primeSlot α c q χ σ₀ σ₁ n‖^2) =
     (∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖sourceEndpoint (sourceOutsidePart allGroupPrimes)
         (sourcePeelingError S V W_hi W_lo)
         primeSlot α c q χ σ₀ σ₁ n‖^2) := by
    exact literal_source_parity_preserves_square_error
      N S Ptwist _
  have hmass := sourcePeelingDifferenceSquareUnion
    allGroupPrimes S W_hi W_lo primeSlot α c N q P χ
    σ₀ σ₁ A C B V vmin L a D
    hA hC hB hα hc hN hP hS hGroups hPrime hLow
    hL hD hv hV hlogN hhi hlo
  calc
    _ ≤ ∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖literalSourceParity Ptwist n *
         sourceEndpoint (sourceOutsidePart allGroupPrimes)
           (sourcePeelingError S V W_hi W_lo)
           primeSlot α c q χ σ₀ σ₁ n‖^2 := by
            simpa only [sourcePeelingResidualFourier] using hF
    _ = ∑ n ∈ sourceSquareExceptionalSupport N S,
       ‖sourceEndpoint (sourceOutsidePart allGroupPrimes)
         (sourcePeelingError S V W_hi W_lo)
         primeSlot α c q χ σ₀ σ₁ n‖^2 := hcount
    _ ≤ _ := hmass
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullPeelingFourier -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Literal source peeling difference over ALL original n∈[1,N]. -/
noncomputable def sourceFullPeelingResidualFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ)
    (k : ℕ)
    (allGroupPrimes primeSlot Ptwist : Finset ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) : C(AddCircle (1:ℝ),ℂ) :=
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (sourcePeelingError S Vs
          (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
          (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k))
        primeSlot α c q χ σ₀ σ₁ n)

/-- Literal source peeling difference is supported precisely at
p²-exceptional positions, hence its global Fourier sum is unchanged
by projection to the exceptional set. -/
theorem source_full_peeling_fourier_eq_exception
    {ι β : Type}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (allGroupPrimes primeSlot Ptwist : Finset ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hTs : ∀ g : ι, ∀ p ∈ Ts g, p.Prime)
    (hDisjS : ∀ g : ι, ∀ p ∈ S, p ∉ Ts g)
    (hTb : ∀ g : β, ∀ p ∈ Tb g, p.Prime)
    (hDisjB : ∀ g : β, ∀ p ∈ S, p ∉ Tb g) :
    sourceFullPeelingResidualFourier
      N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      allGroupPrimes primeSlot Ptwist α c χ σ₀ σ₁ =
    sourcePeelingResidualFourier
      allGroupPrimes S primeSlot Ptwist
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
      (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k)
      Vs α c N q χ σ₀ σ₁ := by
  let W_hi : ℕ → ℂ :=
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1)
  let W_lo : ℕ → ℂ :=
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k
  let F : ℕ → ℂ := fun n => literalSourceParity Ptwist n *
    sourceEndpoint (sourceOutsidePart allGroupPrimes)
      (sourcePeelingError S Vs W_hi W_lo)
      primeSlot α c q χ σ₀ σ₁ n
  have hsubset :
      sourceSquareExceptionalSupport N S ⊆ Finset.Icc 1 N :=
    Finset.filter_subset _ _
  have hzero (n : ℕ)
      (hn : n ∈ Finset.Icc 1 N)
      (hgood : n ∉ sourceSquareExceptionalSupport N S) :
      F n = 0 := by
    have hz := source_physical_peeling_zero_off_exception
      N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k n
      allGroupPrimes primeSlot α c χ σ₀ σ₁
      hS hTs hDisjS hTb hDisjB hn hgood
    dsimp [F,W_hi,W_lo]
    rw [hz]
    simp
  ext theta
  change sourceNatFourierPoly (Finset.Icc 1 N) F theta =
    sourceNatFourierPoly (sourceSquareExceptionalSupport N S)
      F theta
  rw [source_nat_fourier_literal,source_nat_fourier_literal]
  symm
  exact Finset.sum_subset hsubset (by
    intro n hn hnot
    rw [hzero n hn hnot]
    simp)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralPeelingBetaFull -/

section

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open scoped BigOperators
open MeasureTheory

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Fully literal source peeling-difference Fourier energy in a real
beta window. The two source W_hi/W_lo cap assumptions are PROVED
from the ordered BIG mark lists, all small groups and q0 damping.

The parameter K depends only on fixed q0, lower V, and tmax;
there is no arbitrary assumed bound on the marked weight. -/
theorem source_literal_physical_peeling_beta_energy
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        ∀ (N P q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C L a D center H : ℝ),
          0 ≤ A → 0 ≤ C →
          (∀ m, ‖α m‖ ≤ A) →
          (∀ r, ‖c r‖ ≤ C) →
          1 ≤ N → 1 ≤ P →
          S ⊆ Finset.Icc P (2*P) →
          (∀ p ∈ S, p.Prime) →
          Real.exp (L^a)/2 ≤ (P:ℝ) →
          1 ≤ L → 0 ≤ D →
          Real.log (N:ℝ) ≤ D*L →
          2 ≤ H →
          let groupPrimes : Finset ℕ :=
             S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                ((Finset.univ : Finset β).biUnion Tb)
          let W_hi : ℕ → ℂ :=
            literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1)
          let W_lo : ℕ → ℂ :=
            literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k
          let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
          (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
            ‖sourcePeelingResidualFourier
              groupPrimes S primeSlot Ptwist W_hi W_lo Vs
              α c N q χ σ₀ σ₁
              ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
          4*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
            (N:ℝ)*(1+Real.log (N:ℝ))^16*
              Real.exp (-(L^a)) := by
  obtain ⟨K,hK,hweight⟩ :=
    source_literal_weight_uniform_all_groups
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hkPlus hVs hts htb hVsmall hVbig hb
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C L a D center H
    hA hC hα hc hN hP hS hPrime hLow hL hD hlogN hH
  dsimp only
  let groupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  let W_hi : ℕ → ℂ :=
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1)
  let W_lo : ℕ → ℂ :=
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k
  let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hGroups : S ⊆ groupPrimes := by
    intro p hp
    dsimp [groupPrimes]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  have hk : k ≤ tmax := by omega
  have hhi : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ‖W_hi n‖ ≤ B := by
    intro n hn
    exact hweight S Ts Tb Vs Vsmall Vbig ts tb b (k+1) n
      hkPlus hVs hts htb hVsmall hVbig hb
  have hlo : ∀ n ∈ sourceSquareExceptionalSupport N S,
      ∀ p ∈ smallPrimeSupport S n, ‖W_lo (n/p)‖ ≤ B := by
    intro n hn p hp
    exact hweight S Ts Tb Vs Vsmall Vbig ts tb b k (n/p)
      hk hVs hts htb hVsmall hVbig hb
  exact source_physical_peeling_residual_beta_arc
    groupPrimes S primeSlot Ptwist W_hi W_lo Vs
    α c N P q χ σ₀ σ₁ A C B vmin L a D center H
    hA hC hB hα hc hN hP hS hGroups hPrime hLow
    hL hD hv hVs hlogN hhi hlo hH
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullLiteralPeelingBeta -/

section

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Actual literal physical FULL peeling-difference Fourier beta energy.
Unlike the exceptional-projection statement, this controls the original
full sum n∈[1,N] *before* deleting the square exceptional set.

All marked-weight caps are kernel-derived; the extra hypotheses
are exactly the primality/disjointness conditions required for
the original small-prime peeling identity. -/
theorem source_full_literal_physical_peeling_beta_energy
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        (∀ p ∈ S, p.Prime) →
        (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
        (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
        (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
        (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
        ∀ (N P q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C L a D center H : ℝ),
          0 ≤ A → 0 ≤ C →
          (∀ m, ‖α m‖ ≤ A) →
          (∀ r, ‖c r‖ ≤ C) →
          1 ≤ N → 1 ≤ P →
          S ⊆ Finset.Icc P (2*P) →
          Real.exp (L^a)/2 ≤ (P:ℝ) →
          1 ≤ L → 0 ≤ D →
          Real.log (N:ℝ) ≤ D*L →
          2 ≤ H →
          let groupPrimes : Finset ℕ :=
             S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                ((Finset.univ : Finset β).biUnion Tb)
          let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
          (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
            ‖sourceFullPeelingResidualFourier
              N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
              groupPrimes primeSlot Ptwist α c χ σ₀ σ₁
              ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
          4*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2*
            (N:ℝ)*(1+Real.log (N:ℝ))^16*
              Real.exp (-(L^a)) := by
  obtain ⟨K,hK,hBase⟩ :=
    source_literal_physical_peeling_beta_energy
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C L a D center H
    hA hC hα hc hN hP hInterval hLow hL hD hlogN hH
  dsimp only
  let groupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  have hEq := source_full_peeling_fourier_eq_exception
    N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    groupPrimes primeSlot Ptwist α c χ σ₀ σ₁
    hS hTs hDisjS hTb hDisjB
  have hBound := hBase S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C L a D center H
    hA hC hα hc hN hP hInterval hS hLow
    hL hD hlogN hH
  rw [hEq]
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullPeelingRationalFamily -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Source-exact full physical peeling error, summed over every
rational center h/q, q≤Q.  This is the original full [1,N] Fourier
polynomial, with literal marked lists, outside-part core and the
common multiplicity-counted parity twist; no abstract L² surrogate. -/
theorem source_full_literal_peeling_rational_family_energy
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
        k+1 ≤ tmax →
        vmin ≤ Vs →
        (∀ g : ι, ts g ≤ tmax) →
        (∀ g : β, tb g ≤ tmax) →
        (∀ g : ι, vmin ≤ Vsmall g) →
        (∀ g : β, vmin ≤ Vbig g) →
        (∀ lists, ‖b lists‖ ≤ 1) →
        (∀ p ∈ S, p.Prime) →
        (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
        (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
        (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
        (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
        ∀ (N P q : ℕ) (primeSlot Ptwist : Finset ℕ)
          (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
          (σ₀ σ₁ A C L a D H : ℝ) (Q : ℕ),
          0 ≤ A → 0 ≤ C →
          (∀ m, ‖α m‖ ≤ A) →
          (∀ r, ‖c r‖ ≤ C) →
          1 ≤ N → 1 ≤ P →
          S ⊆ Finset.Icc P (2*P) →
          Real.exp (L^a)/2 ≤ (P:ℝ) →
          1 ≤ L → 0 ≤ D →
          Real.log (N:ℝ) ≤ D*L →
          2 ≤ H →
          (∑ center ∈ sourceRationalCenterSet Q,
            ∫ beta in {beta : ℝ | |beta| ≤ 1/H},
              ‖sourceFullPeelingResidualFourier
                N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
                (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                  ((Finset.univ : Finset β).biUnion Tb))
                primeSlot Ptwist α c χ σ₀ σ₁
                ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
          ((Q*(Q+1):ℕ):ℝ) *
            (4*(A*C*(K^(Fintype.card ι + Fintype.card β + 1)*
                L*(1+D/(vmin*Real.log 2))))^2 *
                (N:ℝ)*(1+Real.log (N:ℝ))^16*
                Real.exp (-(L^a))) := by
  obtain ⟨K,hK,hPhysical⟩ :=
    source_full_literal_physical_peeling_beta_energy
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C L a D H Q
    hA hC hα hc hN hP hInterval hLow hL hD hlog hH
  let B : ℝ := K^(Fintype.card ι + Fintype.card β + 1)
  let Bound : ℝ :=
    4*(A*C*(B*L*(1+D/(vmin*Real.log 2))))^2 *
      (N:ℝ)*(1+Real.log (N:ℝ))^16*Real.exp (-(L^a))
  have hBoundPos : 0 ≤ Bound := by
    dsimp [Bound]
    positivity
  have hEvery (center : ℝ) :
      (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖sourceFullPeelingResidualFourier
          N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
          (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
            ((Finset.univ : Finset β).biUnion Tb))
          primeSlot Ptwist α c χ σ₀ σ₁
          ((center+beta) : AddCircle (1:ℝ))‖^2) ≤ Bound := by
    simpa only [Bound,B] using
      (hPhysical S Ts Tb Vs Vsmall Vbig ts tb b k
        hk hVs hts htb hVsmall hVbig hb
        hS hTs hDisjS hTb hDisjB
        N P q primeSlot Ptwist α c χ
        σ₀ σ₁ A C L a D center H
        hA hC hα hc hN hP hInterval hLow hL hD hlog hH)
  have hcard : ((sourceRationalCenterSet Q).card : ℝ) ≤
      ((Q*(Q+1):ℕ):ℝ) := by
    exact_mod_cast source_rational_center_card_le Q
  calc
    _ ≤ ∑ _center ∈ sourceRationalCenterSet Q, Bound := by
      apply Finset.sum_le_sum
      intro center hc
      exact hEvery center
    _ = ((sourceRationalCenterSet Q).card : ℝ)*Bound := by simp
    _ ≤ ((Q*(Q+1):ℕ):ℝ)*Bound :=
      mul_le_mul_of_nonneg_right hcard hBoundPos
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullPeelingRationalSavings -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- The full literal physical peeling Fourier error over all source
rational arcs has a concrete polylogarithmic prefactor, rather than
merely a scalar budget. The only structural assumptions are the
source disjoint-prime groups, fixed mark cap and bounded big-mark test. -/
theorem source_full_literal_peeling_rational_log_budget
    (q0 vmin C0 D E ArcExp : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1)
    (hv : 0 < vmin) (hC0 : 0 ≤ C0)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hArcExp : 0 ≤ ArcExp) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (L : ℝ), 1 ≤ L →
        ∀ {ι β : Type}
          [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β]
          (S : Finset ℕ) (Ts : ι → Finset ℕ)
          (Tb : β → Finset ℕ)
          (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
          (ts : ι → ℕ) (tb : β → ℕ)
          (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
          k+1 ≤ tmax →
          vmin ≤ Vs →
          (∀ g : ι, ts g ≤ tmax) →
          (∀ g : β, tb g ≤ tmax) →
          (∀ g : ι, vmin ≤ Vsmall g) →
          (∀ g : β, vmin ≤ Vbig g) →
          (∀ lists, ‖b lists‖ ≤ 1) →
          (∀ p ∈ S, p.Prime) →
          (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
          (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
          (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
          (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
          (Fintype.card ι : ℝ) ≤ C0*Real.log L →
          (Fintype.card β : ℝ) ≤ C0*Real.log L →
          K*(1+D/(vmin*Real.log 2)) ≤ L →
          ∀ (N P q : ℕ) (primeSlot Ptwist : Finset ℕ)
            (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
            (σ₀ σ₁ A C a Y H : ℝ) (Q : ℕ),
            0 ≤ A → 0 ≤ C →
            (∀ m, ‖α m‖ ≤ A) →
            (∀ r, ‖c r‖ ≤ C) →
            1 ≤ N → 1 ≤ P →
            S ⊆ Finset.Icc P (2*P) →
            Real.exp (L^a)/2 ≤ (P:ℝ) →
            (N:ℝ) ≤ Y →
            A ≤ L^E → C ≤ L^E →
            Real.log (N:ℝ) ≤ D*L →
            (Q:ℝ) ≤ L^ArcExp → 2 ≤ H →
            (∑ center ∈ sourceRationalCenterSet Q,
              ∫ beta in {beta : ℝ | |beta| ≤ 1/H},
                ‖sourceFullPeelingResidualFourier
                  N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
                  (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                    ((Finset.univ : Finset β).biUnion Tb))
                  primeSlot Ptwist α c χ σ₀ σ₁
                  ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
            Y*(8*(1+D)^16*
               L^(4*E+2*(2*C0*Real.log K+2)+16+2*ArcExp)*
               Real.exp (-(L^a))) := by
  obtain ⟨K,hK,hFamily⟩ :=
    source_full_literal_peeling_rational_family_energy
      q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro L hL ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB
    hSmall hBig hLarge
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C a Y H Q
    hA hC hα hc hN hP hInt hLow hNY hAb hCb hLog hQ hH
  have hNreal : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hFam := hFamily S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB
    N P q primeSlot Ptwist α c χ
    σ₀ σ₁ A C L a D H Q
    hA hC hα hc hN hP hInt hLow hL hD hLog hH
  have hScalar := source_literal_peeling_rational_scalar_budget
    K L C0 D vmin A C (N:ℝ) Y E a ArcExp
    (Fintype.card ι) (Fintype.card β) Q
    hK hL hC0 hD hv hArcExp hSmall hBig hLarge
    hNreal hNY hA hC hE hAb hCb hLog hQ
  exact hFam.trans (by simpa only [mul_assoc] using hScalar)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullPeelingOriginalArcs -/

section

open Filter Real
open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Complete source physical *full peeling error* budget at the
original U1 U2, H'=U1 U2, H=H'/L^Carc and q≤|k|L^B
rational arcs. The coefficient is the actual Fourier polynomial
over [1,N]; no mean-square hypothesis is assumed. This result
does NOT bound the main nonexceptional endpoint energy. -/
theorem eventually_source_full_literal_peeling_original_arcs_negligible
    (q0 vmin C0 D E : ℝ) (tmax : ℕ)
    (a c B Kshift Carc C₁ C₂ Target : ℝ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : 0 < a) (hc : 0 < c)
    (hB : 0 ≤ B) (hKshift : 0 ≤ Kshift) :
    ∃ Kmark : ℝ, 1 ≤ Kmark ∧
      ∀ᶠ L : ℝ in atTop,
        2 ≤ L ∧
        ∀ (U1 U2 Hprime : ℝ),
          Real.exp (L^c-C₁) ≤ U1 →
          Real.exp (L^c-C₂) ≤ U2 →
          Hprime = U1*U2 →
          ∀ {ι β : Type}
            [Fintype ι] [DecidableEq ι]
            [Fintype β] [DecidableEq β]
            (S : Finset ℕ) (Ts : ι → Finset ℕ)
            (Tb : β → Finset ℕ)
            (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
            (ts : ι → ℕ) (tb : β → ℕ)
            (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
            k+1 ≤ tmax →
            vmin ≤ Vs →
            (∀ g : ι, ts g ≤ tmax) →
            (∀ g : β, tb g ≤ tmax) →
            (∀ g : ι, vmin ≤ Vsmall g) →
            (∀ g : β, vmin ≤ Vbig g) →
            (∀ lists, ‖b lists‖ ≤ 1) →
            (∀ p ∈ S, p.Prime) →
            (∀ g : ι, ∀ p ∈ Ts g, p.Prime) →
            (∀ g : ι, ∀ p ∈ S, p ∉ Ts g) →
            (∀ g : β, ∀ p ∈ Tb g, p.Prime) →
            (∀ g : β, ∀ p ∈ S, p ∉ Tb g) →
            (Fintype.card ι : ℝ) ≤ C0*Real.log L →
            (Fintype.card β : ℝ) ≤ C0*Real.log L →
            ∀ (N P q : ℕ) (primeSlot Ptwist : Finset ℕ)
              (α cseq : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
              (σ₀ σ₁ A C Y : ℝ),
              0 ≤ A → 0 ≤ C →
              (∀ m, ‖α m‖ ≤ A) →
              (∀ r, ‖cseq r‖ ≤ C) →
              1 ≤ N → 1 ≤ P →
              S ⊆ Finset.Icc P (2*P) →
              Real.exp (L^a)/2 ≤ (P:ℝ) →
              (N:ℝ) ≤ Y →
              A ≤ L^E → C ≤ L^E →
              Real.log (N:ℝ) ≤ D*L →
              (∑ center ∈ sourceRationalCenterSet ⌈L^(B+Kshift+1)⌉₊,
                ∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
                  ‖sourceFullPeelingResidualFourier
                    N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
                    (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                      ((Finset.univ : Finset β).biUnion Tb))
                    primeSlot Ptwist α cseq χ σ₀ σ₁
                    ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
              Y/L^Target := by
  have hArcExp : 0 ≤ B+Kshift+2 := by linarith
  obtain ⟨Kmark,hKmark,hFamily⟩ :=
    source_full_literal_peeling_rational_log_budget
      q0 vmin C0 D E (B+Kshift+2) tmax
      hq0 hq1 hv hC0 hD hE hArcExp
  have hWindow := eventually_source_major_arc_window_at_least_two
    c Carc C₁ C₂ hc
  let Exponent : ℝ :=
    4*E+2*(2*C0*Real.log Kmark+2)+16+2*(B+Kshift+2)
  have hSave := eventually_source_fixed_poly_exp_saving
    a (8*(1+D)^16) Exponent Target ha
  have hMarkLarge := eventually_ge_atTop
    (max (2:ℝ) (Kmark*(1+D/(vmin*Real.log 2))))
  refine ⟨Kmark,hKmark,?_⟩
  filter_upwards [hWindow,hSave,hMarkLarge] with L hWindowL hSaveL hLargeL
  obtain ⟨hLsave,hScalar⟩ := hSaveL
  obtain ⟨hLWindow,hWindowBase⟩ := hWindowL
  have hL : 2 ≤ L := (le_max_left _ _).trans hLargeL
  have hLone : 1 ≤ L := by linarith
  have hMark : Kmark*(1+D/(vmin*Real.log 2)) ≤ L :=
    (le_max_right _ _).trans hLargeL
  have hExp : 0 ≤ B+Kshift+1 := by linarith
  have hQbound : (⌈L^(B+Kshift+1)⌉₊:ℝ) ≤ L^(B+Kshift+2) := by
    convert source_ceil_polylog_cap L (B+Kshift+1) hL hExp using 1
    congr 1
    ring
  refine ⟨hL,?_⟩
  intro U1 U2 Hprime hU1 hU2 hH
  have hWindowSize : 2 ≤ Hprime/L^Carc :=
    hWindowBase U1 U2 Hprime hU1 hU2 hH
  have hLp : 0 < L := by linarith
  have hLC : 0 < L^Carc := Real.rpow_pos_of_pos hLp Carc
  have hHp : 0 < Hprime := by
    have hh := mul_pos (by linarith : 0 < Hprime/L^Carc) hLC
    have hEq : (Hprime/L^Carc)*L^Carc=Hprime :=
      div_mul_cancel₀ Hprime hLC.ne'
    linarith
  intro ι β _ _ _ _ S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB hSmall hBig
    N P q primeSlot Ptwist α cseq χ
    σ₀ σ₁ A C Y hA hC hα hc hN hP hInt hLow
    hNY hAb hCb hLog
  have hY : 0 ≤ Y := by
    have hNreal : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hBound := hFamily L hLone S Ts Tb Vs Vsmall Vbig ts tb b k
    hk hVs hts htb hVsmall hVbig hb
    hS hTs hDisjS hTb hDisjB hSmall hBig hMark
    N P q primeSlot Ptwist α cseq χ
    σ₀ σ₁ A C a Y (Hprime/L^Carc) ⌈L^(B+Kshift+1)⌉₊
    hA hC hα hc hN hP hInt hLow hNY hAb hCb hLog
    hQbound hWindowSize
  have hSmallBound :
      Y*(8*(1+D)^16*L^Exponent*Real.exp (-(L^a))) ≤
        Y/L^Target := by
    calc
      _ ≤ Y*(1/L^Target) :=
        mul_le_mul_of_nonneg_left hScalar hY
      _ = Y/L^Target := by ring
  have hRad : (1:ℝ)/(Hprime/L^Carc) = L^Carc/Hprime := by
    field_simp
  simpa only [hRad,Exponent] using hBound.trans hSmallBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFullPeelingEndpointBridge -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Original physical endpoint Fourier polynomial *before* small-prime
peeling. Exact outside core, full source marks and parity, no
squarefree restriction and no coefficient renormalization. -/
noncomputable def sourceFullMarkedFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    C(AddCircle (1:ℝ),ℂ) :=
  let allGroupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
        primeSlot α c q χ σ₀ σ₁ n)

/-- Exactly the endpoint after extracting the designated small-group
mark. The original core and parity stay at n, while only the remaining
small-prime marked weight is evaluated at n/p. -/
noncomputable def sourcePeeledMarkedFourier
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    C(AddCircle (1:ℝ),ℂ) :=
  let allGroupPrimes : Finset ℕ :=
    S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)
  sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => literalSourceParity Ptwist n *
      sourceEndpoint (sourceOutsidePart allGroupPrimes)
        (fun n => ((1/Vs:ℝ):ℂ) *
           ∑ p ∈ smallPrimeSupport S n,
             literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k (n/p))
        primeSlot α c q χ σ₀ σ₁ n)

/-- Exact, global *source physical* Fourier identity:
raw endpoint = peeled endpoint + full exceptional square residual.
All frequency centers and signs are allowed. No estimates or
squarefree hypotheses enter this algebraic identity. -/
theorem source_full_marked_fourier_eq_peeled_add_error
    {ι β : Type}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (theta : AddCircle (1:ℝ)) :
    sourceFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ theta =
    sourcePeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ theta +
    sourceFullPeelingResidualFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
         ((Finset.univ : Finset β).biUnion Tb))
      primeSlot Ptwist α c χ σ₀ σ₁ theta := by
  classical
  simp only [sourceFullMarkedFourier,sourcePeeledMarkedFourier,
     sourceFullPeelingResidualFourier,source_nat_fourier_literal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sourceEndpoint,sourcePeelingError]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeeledLiteralCoefficient -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Genuine normalized Haar extraction of an original finite source
Fourier coefficient, rather than an L² or norm surrogate. -/
theorem source_nat_fourier_coeff_exact
    (S : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    fourierCoeff (T := 1) (sourceNatFourierPoly S F) (n:ℤ) =
      if n ∈ S then F n else 0 := by
  classical
  have hfun : (sourceNatFourierPoly S F : AddCircle (1:ℝ) → ℂ) =
      fun theta => ∑ k ∈ S, F k * fourier (T := 1) (k:ℤ) theta := by
    funext theta
    exact source_nat_fourier_literal S F theta
  rw [hfun]
  have hi : ∀ k ∈ S, Integrable
      (fun theta : AddCircle (1:ℝ) =>
        F k * fourier (T := 1) (k:ℤ) theta)
      AddCircle.haarAddCircle := by
    intro k hk
    exact (continuous_const.mul (fourier (T := 1) (k:ℤ)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : (fun theta : AddCircle (1:ℝ) =>
      ∑ k ∈ S, F k * fourier (T := 1) (k:ℤ) theta) =
      ∑ k ∈ S, (fun theta : AddCircle (1:ℝ) =>
        F k * fourier (T := 1) (k:ℤ) theta) := by
    funext theta
    simp only [Finset.sum_apply]
  rw [hsum]
  rw [fourierCoeff.sum S
    (fun k (theta : AddCircle (1:ℝ)) =>
      F k * fourier (T := 1) (k:ℤ) theta) hi]
  have hterm (k : ℕ) :
      fourierCoeff (T := 1)
        (fun theta : AddCircle (1:ℝ) =>
          F k * fourier (T := 1) (k:ℤ) theta) (n:ℤ) =
      F k * (if k = n then 1 else 0) := by
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
    by_cases h : k = n
    · subst k
      simp
    · have hk : (k:ℤ) ≠ (n:ℤ) := by exact_mod_cast h
      simp [h, hk]
  rw [Finset.sum_apply]
  simp_rw [hterm]
  simp [Finset.sum_ite_eq']

/-- Exact *extracted* coefficient of the original source peeled
Fourier polynomial, before any splitting of m,p_s,p,r'. In
particular all 1/Vs, outside-part, sign, character, and big/small
mark factors are visible and are not replaced by their norms. -/
theorem source_peeled_fourier_coefficient_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (n : ℕ) :
    fourierCoeff (T := 1)
      (sourcePeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot Ptwist α c χ σ₀ σ₁) (n:ℤ) =
      if n ∈ Finset.Icc 1 N then
        literalSourceParity Ptwist n *
          sourceEndpoint
            (sourceOutsidePart (S ∪
              ((Finset.univ : Finset ι).biUnion Ts) ∪
              ((Finset.univ : Finset β).biUnion Tb)))
            (fun z => ((1/Vs:ℝ):ℂ) *
              ∑ ps ∈ smallPrimeSupport S z,
                literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
                  ts tb b k (z/ps))
            primeSlot α c q χ σ₀ σ₁ n
      else 0 := by
  classical
  simpa only [sourcePeeledMarkedFourier] using
    (source_nat_fourier_coeff_exact (Finset.Icc 1 N)
      (fun z => literalSourceParity Ptwist z *
        sourceEndpoint
          (sourceOutsidePart (S ∪
            ((Finset.univ : Finset ι).biUnion Ts) ∪
            ((Finset.univ : Finset β).biUnion Tb)))
          (fun z => ((1/Vs:ℝ):ℂ) *
            ∑ ps ∈ smallPrimeSupport S z,
              literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
                ts tb b k (z/ps))
          primeSlot α c q χ σ₀ σ₁ z) n)

/-- Exact triple-divisor coefficient extracted from the source
Fourier polynomial. All divisibility, prime-slot, big/small marks,
sourceOutsidePart and literal parity choices remain in the statement.
The unsolved part is reindexing this actual sum into m*p_s*p*r'
with literal sourcePhysicalMarkedResidual. -/
theorem source_peeled_fourier_triple_coefficient_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (n : ℕ) :
    fourierCoeff (T := 1)
      (sourcePeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot Ptwist α c χ σ₀ σ₁) (n:ℤ) =
      if n ∈ Finset.Icc 1 N then
        literalSourceParity Ptwist n *
        ((∑ m ∈ (sourceOutsidePart
           (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                 ((Finset.univ : Finset β).biUnion Tb)) n).divisors,
          ∑ p ∈ (sourceOutsidePart
           (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                 ((Finset.univ : Finset β).biUnion Tb)) n).divisors,
            if p ∈ primeSlot ∧ p.Prime ∧
                 m*p ∣ sourceOutsidePart
                  (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                    ((Finset.univ : Finset β).biUnion Tb)) n then
              α m * χ m * sourceUnitTwist m σ₀ *
                sourceUnitTwist p σ₁ *
              c ((sourceOutsidePart
                (S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                  ((Finset.univ : Finset β).biUnion Tb)) n)/(m*p))
            else 0) *
         (((1/Vs:ℝ):ℂ) *
            ∑ ps ∈ smallPrimeSupport S n,
              literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
                ts tb b k (n/ps)))
      else 0 := by
  classical
  simpa only [sourceEndpoint,sourceCore] using
    (source_peeled_fourier_coefficient_exact
      N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot Ptwist α c χ σ₀ σ₁ n)
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeeledLiteralFactorLemmas -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- The source parity with valuation multiplicity is genuinely
completely multiplicative on positive integers, not merely unimodular. -/
theorem literal_source_parity_mul_exact (P : Finset ℕ)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    literalSourceParity P (m*n) =
      literalSourceParity P m * literalSourceParity P n := by
  classical
  simp only [literalSourceParity, Nat.factorization_mul hm hn,
    Finsupp.add_apply, Finset.sum_add_distrib, pow_add]

/-- The full valuation-counted parity is exactly trivial on numbers
with no prime valuation in the indicated source group. -/
theorem literal_source_parity_eq_one_of_no_group_factor
    (P : Finset ℕ) (n : ℕ)
    (hNo : ∀ p ∈ P, n.factorization p = 0) :
    literalSourceParity P n = 1 := by
  simp [literalSourceParity, Finset.sum_eq_zero hNo]

/-- The literal sign retained on p_s and r' after moving m,p
outside the sign-support groups. Both prescribed parity options
remain valid, including P=∅. -/
theorem literal_source_fourfactor_parity_exact (P : Finset ℕ)
    (m ps p r : ℕ)
    (hm : m ≠ 0) (hps : ps ≠ 0)
    (hp : p ≠ 0) (hr : r ≠ 0)
    (hM : ∀ x ∈ P, m.factorization x = 0)
    (hP : ∀ x ∈ P, p.factorization x = 0) :
    literalSourceParity P (m*ps*p*r) =
      literalSourceParity P ps * literalSourceParity P r := by
  have hmp : m*ps ≠ 0 := mul_ne_zero hm hps
  have hmpp : (m*ps)*p ≠ 0 := mul_ne_zero hmp hp
  rw [literal_source_parity_mul_exact P _ _ hmpp hr,
      literal_source_parity_mul_exact P _ _ hmp hp,
      literal_source_parity_mul_exact P _ _ hm hps,
      literal_source_parity_eq_one_of_no_group_factor P m hM,
      literal_source_parity_eq_one_of_no_group_factor P p hP]
  ring

/-- The literal outside part is the multiplicative part of the
factorization supported on non-group primes. -/
theorem source_outside_part_as_factorization
    (G : Finset ℕ) (n : ℕ) :
    sourceOutsidePart G n =
      n.factorization.prod (fun p e => if p ∈ G then 1 else p^e) := by
  classical
  unfold sourceOutsidePart Finsupp.prod
  simp only [Nat.support_factorization]
  rw [Finset.prod_ite]
  simp

/-- Exact multiplicativity of the source outside-part, including
prime powers and all group sets (for positive inputs). -/
theorem source_outside_part_mul
    (G : Finset ℕ) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    sourceOutsidePart G (m*n) =
      sourceOutsidePart G m * sourceOutsidePart G n := by
  simp only [source_outside_part_as_factorization,
    Nat.factorization_mul hm hn]
  apply Finsupp.prod_add_index'
  · intro p
    split_ifs <;> simp
  · intro p a b
    split_ifs <;> simp [pow_add]

/-- A number consisting only of primes outside the marked groups
survives the original outside-part operation *exactly*. -/
theorem source_outside_part_eq_self_of_no_group_primes
    (G : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hNo : ∀ p ∈ n.primeFactors, p ∉ G) :
    sourceOutsidePart G n = n := by
  classical
  unfold sourceOutsidePart
  rw [Finset.filter_eq_self.mpr hNo]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

/-- A number with every prime divisor in a marked group is removed
completely by the literal outside-part operation. -/
theorem source_outside_part_eq_one_of_group_primes
    (G : Finset ℕ) (n : ℕ)
    (hAll : n.primeFactors ⊆ G) :
    sourceOutsidePart G n = 1 := by
  classical
  unfold sourceOutsidePart
  have hz : (n.primeFactors.filter (fun p => p ∉ G)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    simpa using hAll hp
  rw [hz]
  simp

/-- Exact replacement of the outside-part of m p_s p r' by
m p times the outside-part of r'; the three support conditions
are structural (not analytic energy or norm hypotheses). -/
theorem source_outside_part_fourfactor_exact
    (G : Finset ℕ) (m ps p r : ℕ)
    (hm : m ≠ 0) (hps : ps ≠ 0) (hp : p ≠ 0) (hr : r ≠ 0)
    (hmNo : ∀ v ∈ m.primeFactors, v ∉ G)
    (hpNo : ∀ v ∈ p.primeFactors, v ∉ G)
    (hpsAll : ps.primeFactors ⊆ G) :
    sourceOutsidePart G (m*ps*p*r) =
      m*p*sourceOutsidePart G r := by
  have hmp : m*ps ≠ 0 := mul_ne_zero hm hps
  have hmpp : (m*ps)*p ≠ 0 := mul_ne_zero hmp hp
  rw [source_outside_part_mul G _ _ hmpp hr,
    source_outside_part_mul G _ _ hmp hp,
    source_outside_part_mul G _ _ hm hps,
    source_outside_part_eq_self_of_no_group_primes G m hm hmNo,
    source_outside_part_eq_one_of_group_primes G ps hpsAll,
    source_outside_part_eq_self_of_no_group_primes G p hp hpNo]
  ring

/-- For an actual selected group prime p_s, the source
outside-part completely discards it, at every multiplicity. -/
theorem source_outside_part_group_prime
    (G : Finset ℕ) (ps : ℕ) (hps : ps.Prime) (hpsG : ps ∈ G) :
    sourceOutsidePart G ps = 1 := by
  apply source_outside_part_eq_one_of_group_primes
  intro v hv
  obtain ⟨hvPrime, hvDvd, _⟩ := Nat.mem_primeFactors.mp hv
  have hvEq : v = ps := (Nat.prime_dvd_prime_iff_eq hvPrime hps).mp hvDvd
  simpa [hvEq] using hpsG

/-- The actual original source core coefficient c(n_*/(m p))
becomes exactly c(r'_*) for each rough quadruple, with no
norm replacement or squarefree assumptions on r'. -/
theorem source_outside_part_fourfactor_div_exact
    (G : Finset ℕ) (m ps p r : ℕ)
    (hm : m ≠ 0) (hps : ps ≠ 0) (hp : p ≠ 0) (hr : r ≠ 0)
    (hmNo : ∀ v ∈ m.primeFactors, v ∉ G)
    (hpNo : ∀ v ∈ p.primeFactors, v ∉ G)
    (hpsAll : ps.primeFactors ⊆ G) :
    (sourceOutsidePart G (m*ps*p*r))/(m*p) =
      sourceOutsidePart G r := by
  rw [source_outside_part_fourfactor_exact G m ps p r
    hm hps hp hr hmNo hpNo hpsAll]
  exact Nat.mul_div_cancel_left _ (mul_pos
    (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hp))
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePeeledLiteralWeightCongruence -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationD

/-- Literal support is unchanged on multiplying by a factor containing
none of the primes of T. No squarefree assumption on either factor. -/
theorem source_small_prime_support_mul_rough
    (T : Finset ℕ) (m r : ℕ)
    (hPrime : ∀ p ∈ T, p.Prime)
    (hRough : ∀ p ∈ T, ¬ p ∣ m) :
    smallPrimeSupport T (m*r) = smallPrimeSupport T r := by
  classical
  ext p
  by_cases hp : p ∈ T
  · have hprime := hPrime p hp
    simp only [smallPrimeSupport, Finset.mem_filter, hp, true_and]
    constructor
    · intro hpdiv
      rcases (hprime.dvd_mul).mp hpdiv with hm | hr
      · exact (hRough p hp hm).elim
      · exact hr
    · intro hr
      exact dvd_mul_of_dvd_right hr m
  · simp [smallPrimeSupport, hp]

/-- The full big-group ordered-mark decoration depends only on the
exact prime supports in its groups. -/
theorem source_big_mark_decoration_congr_support
    {β : Type} [Fintype β] [DecidableEq β]
    (Tb : β → Finset ℕ) (tb : β → ℕ)
    (q0 : ℝ) (Vbig : β → ℝ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ)
    (n r : ℕ)
    (hSupport : ∀ g : β,
      smallPrimeSupport (Tb g) n = smallPrimeSupport (Tb g) r) :
    actualBigMarkDecoration Tb tb q0 Vbig b n =
      actualBigMarkDecoration Tb tb q0 Vbig b r := by
  have hCount (g : β) : smallPrimeCount (Tb g) n =
      smallPrimeCount (Tb g) r := congrArg Finset.card (hSupport g)
  have hPref : bigMarkPrefactor Tb tb q0 Vbig n =
      bigMarkPrefactor Tb tb q0 Vbig r := by
    unfold bigMarkPrefactor
    apply Finset.prod_congr rfl
    intro g hg
    rw [hCount g]
  have hList : bigMarkLists Tb tb n = bigMarkLists Tb tb r := by
    unfold bigMarkLists
    congr 1
    funext g
    unfold orderedBigMarks
    rw [hSupport g]
  unfold actualBigMarkDecoration
  rw [hPref, hList]

/-- All literal factors including the selected group, every remaining
small group, every big ordered-mark list and their 1/V_g factors
depend ONLY on the marked prime supports; no norm comparison. -/
theorem literal_source_weight_congr_support
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ)
    (k n r : ℕ)
    (hS : smallPrimeSupport S n = smallPrimeSupport S r)
    (hTs : ∀ g : ι, smallPrimeSupport (Ts g) n =
       smallPrimeSupport (Ts g) r)
    (hTb : ∀ g : β, smallPrimeSupport (Tb g) n =
       smallPrimeSupport (Tb g) r) :
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k n =
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r := by
  have hSCount : smallPrimeCount S n = smallPrimeCount S r :=
    congrArg Finset.card hS
  have hTCount (g : ι) :
      smallPrimeCount (Ts g) n = smallPrimeCount (Ts g) r :=
    congrArg Finset.card (hTs g)
  have hSelected :
      smallMarkedWeight S q0 Vs k n =
      smallMarkedWeight S q0 Vs k r := by
    simp only [smallMarkedWeight, smallMarkKernel, hSCount]
  have hOther :
      otherGroupWeight (Finset.univ : Finset ι)
        Ts q0 Vsmall ts n =
      otherGroupWeight (Finset.univ : Finset ι)
        Ts q0 Vsmall ts r := by
    unfold otherGroupWeight
    apply Finset.prod_congr rfl
    intro g _
    congr 1
    simp only [smallMarkedWeight, smallMarkKernel, hTCount g]
  have hBig := source_big_mark_decoration_congr_support
    Tb tb q0 Vbig b n r hTb
  rw [← sourceMarkedWeight_eq_literal,
      ← sourceMarkedWeight_eq_literal]
  simp only [sourceMarkedWeight, hSelected, hOther, hBig]

/-- Removing a rough multiplier from the FULL literal source
marked weight preserves its complex value, not merely its norm. -/
theorem literal_source_weight_mul_rough
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ)
    (k m r : ℕ)
    (hSprime : ∀ p ∈ S, p.Prime)
    (hTsprime : ∀ g, ∀ p ∈ Ts g, p.Prime)
    (hTbprime : ∀ g, ∀ p ∈ Tb g, p.Prime)
    (hSrough : ∀ p ∈ S, ¬ p ∣ m)
    (hTsrough : ∀ g, ∀ p ∈ Ts g, ¬ p ∣ m)
    (hTbrough : ∀ g, ∀ p ∈ Tb g, ¬ p ∣ m) :
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k (m*r) =
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r := by
  apply literal_source_weight_congr_support
    S Ts Tb q0 Vs Vsmall Vbig ts tb b k (m*r) r
  · exact source_small_prime_support_mul_rough
      S m r hSprime hSrough
  · intro g
    exact source_small_prime_support_mul_rough
      (Ts g) m r (hTsprime g) (hTsrough g)
  · intro g
    exact source_small_prime_support_mul_rough
      (Tb g) m r (hTbprime g) (hTbrough g)
end Green64Analytic.CorrelationD

end

