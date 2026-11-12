module

public import Green64.Library.Sieve.Foundations.Part034
public import Green64.Library.Weights.Part005
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part033
public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part026

@[expose] public section

/-!
# Sieve / Foundations / Part035

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalLowfreqSigmaPsiTwistedFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- FULL ORIGINAL Parity(4.16) on the TRUE positive Sigma divisor
carrier with the concrete C-infinity dyadic ψ_Z is EXACTLY the
unrestricted original B633 Fourier correlator inside the genuine
physical 3D Fourier transform source, at EACH frequency ζ.
No per-character ghost removal or Fourier truncation is done:
this is a pointwise equality for arbitrary real log inputs U,Z,
complex prime residual, original χ, signed epsilon and W1. -/
theorem parity_original_historical_actual_positive_sigma_psi_twisted_eq_full_fourier434
    (L rho xi1 xi2 xi3 U Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (signed : Bool) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (ζ : EuclideanSpace ℝ (Fin 3)) :
    parityOriginal3DPhysicalFiniteTwistedSource434
      (parityOriginalHistoricalActualB633PositiveSigma434 L k N)
      (fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat))
      (fun i => parityOriginalHistoricalRealLogTriple434 U Z
        i.2.2 i.2.1 i.1) f ζ =
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      parityOriginalHistoricalActualB633FullFourierCofactor434
        L rho xi1 xi2 xi3 U Z k N alpha residual q chi lo hi signed
        parityOriginalHistoricalDyadicSmoothPsi434 ζ := by
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
  rw [parity_original_historical_actual_B633_positive_sigma_psi_fourier_exact434]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSigmaPsiOriginalEq417Ball -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2650000

/-- ORIGINAL Parity (4.17) genuine complete positive Sigma
ψ(z/Z) low-frequency B633 physical source bound, now with the
literal unrestricted double-cofactor B633 Fourier correlator in
the right side (rather than an abstract finite twisted-source).
For each original k,Z, all native B509/H0, fine b629 alpha, W1,
ε and source eta_e eta_n remain inside the exact source signal.
The COMPLETE chi sum precedes source/ghost filtering and norms;
the missing ghost is paid by its actual positive ψ-weighted mass
and M_H(f)/T^H. This does NOT yet bound the Fourier-ball integral
by Z L^-D or sum over k/Z/branch families. -/
theorem parity_eventually_original_actual_B633_positive_sigma_psi_ball_le_original_eq417434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ (N : Finset ℕ), (∀ z∈N,0<z) →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let m : I → ℕ := fun i => i.2.2
      let mp : I → ℕ := fun i => i.2.1
      let z : I → ℕ := fun i => i.1
      let zp : I → ℕ := fun i => (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let good : I → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : I → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : I → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                  (2*k.natAbs) chi 0 0
               parityOriginalHistoricalActualB633FullFourierCofactor434
                 L rho xi1 xi2 xi3 U Z k N alpha F.residual
                 (2*k.natAbs) chi F.lo F.hi signed
                 parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        ((s.filter good).filter (fun i => ¬physical i)) Wproj *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_actual_B633_positive_sigma_psi_ball_le_full_chi434
      S beta gamma Ck hS hbeta hgamma] with L hOld
  refine ⟨hOld.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN buf a b hSmooth hBufSupport H T hT
  have hBound := hOld.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN buf a b hSmooth hBufSupport H T hT
  dsimp only at hBound ⊢
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) :=
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hLw U E V Z k buf a b hSmooth hBufSupport
  let Fchi (chi : DirichletCharacter ℂ (2*k.natAbs)) :=
    sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let Wchi (chi : DirichletCharacter ℂ (2*k.natAbs)) : I → ℂ :=
    fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha (Fchi chi).residual
        (2*k.natAbs) chi (Fchi chi).lo (Fchi chi).hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  have hEach (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ) =
      (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha (Fchi chi).residual
          (2*k.natAbs) chi (Fchi chi).lo (Fchi chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ) := by
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact parity_original_historical_actual_positive_sigma_psi_twisted_eq_full_fourier434
      L rho xi1 xi2 xi3 U Z k N alpha (Fchi chi).residual (2*k.natAbs)
      chi (Fchi chi).lo (Fchi chi).hi signed f ζ
  have hSum : (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434 s (Wchi chi) t f ζ)) =
    (∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          parityOriginalHistoricalActualB633FullFourierCofactor434
            L rho xi1 xi2 xi3 U Z k N alpha (Fchi chi).residual
            (2*k.natAbs) chi (Fchi chi).lo (Fchi chi).hi signed
            parityOriginalHistoricalDyadicSmoothPsi434 ζ)) := by
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [hEach chi]
  rw [hSum] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullChiGhostMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact finite Parity(2.6) character-first absolute cofactor mass
bound, retaining each genuine character coefficient rather than
paying the number of characters after a signed projection. Valid
for arbitrary complex B633 two-core pair weights, not requiring
positivity or separate physical e/n masks. -/
theorem parity_original_full_character_projected_pair_mass_le_weighted434
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℤ)
    (W : DirichletCharacter ℂ (2*k.natAbs) → ι → ℂ) :
    (∑i∈S, ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi i‖) ≤
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
        (∑i∈S, ‖W chi i‖) := by
  calc
    _ ≤ ∑i∈S, ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi i‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
    _ = ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          ∑i∈S, ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
            ‖W chi i‖ := by
          simp_rw [norm_mul]
          exact Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro chi hchi
          rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSigmaGhostMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The ORIGINAL complete positive Parity(4.16)-(4.17) cofactor Σ
(z,m',m), all actual B509/H0 prime-slot, P-W1, parity and true
fine b629 α, signed k, with the literal constructed dyadic ψ_Z:
the absolute mass of the WHOLE projected odd-e cofactor pair
is bounded by the χ-WEIGHTED SUM of absolute masses of genuine
original B633 individual pair coefficients, with no #χ, #e, #m,
#z or signed-subsum inference. The coefficient cχ is the native
1/φ(2|k|) original Parity mask with known total ℓ1 mass ≤1.

This is a full source-specific *positive pair mass* bound. It
is deliberately NOT replaced by the smaller absolute value of
the whole Parity correlation: obtaining an explicit polynomial bound
on each χ-weighted positive pair mass from the original H0/b629
arithmetic remains an analytical/formal debt. -/
theorem parity_eventually_original_positive_sigma_projected_B633_mass_le_real_chi_pair_mass434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 Z : ℝ) (signed : Bool) (N : Finset ℕ),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i =>
        parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let Wproj : I → ℂ := fun i => g i * (A i*alpha i.2.2*star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
         then (1:ℂ) else 0))
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      (∑i∈s, ‖Wproj i‖) ≤
        ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
          (∑i∈s, ‖Wchi chi i‖) := by
  filter_upwards [parity_eventually_original_actual_B633_pointwise_full_chi434
      S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 Z signed N
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Wproj : I → ℂ := fun i => g i*(A i*alpha i.2.2*star (alpha i.2.1)*
    (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
     then (1:ℂ) else 0))
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    g i * parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  have hPair (i : I) : Wproj i =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi*Wchi chi i := by
    have hP := hProj.2 prime l u hl hlow K k hk hkBound
      d band slot δ ξ rho xi1 xi2 xi3 signed
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
    dsimp only at hP
    change (A i*alpha i.2.2*star (alpha i.2.1))*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
       then (1:ℂ) else 0) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
            (2*k.natAbs) chi 0 0
           parityOriginalHistoricalB633PhysicalPairTerm434
            L rho xi1 xi2 xi3 signed alpha F.residual
            (2*k.natAbs) chi F.lo F.hi
            i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)) at hP
    change g i * ((A i*alpha i.2.2*star (alpha i.2.1))*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
       then (1:ℂ) else 0)) = _
    rw [hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    dsimp [Wchi]
    ring
  calc
    _ = ∑i∈s, ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi * Wchi chi i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        change ‖Wproj i‖ = ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi * Wchi chi i‖
        rw [hPair i]
    _ ≤ _ := parity_original_full_character_projected_pair_mass_le_weighted434 s k Wchi
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSigmaGhostMassSubset -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- ACTUAL Parity(4.16)-(4.17) original ψ_Z physical or nonphysical
Sigma complement: the absolute total mass of ANY ghost subset of
the genuine unrestricted P-ordinary divisor Σ is controlled by
the χ-weighted FULL POSITIVE individual original B633 two-core
pair mass. This uses only a genuine nonnegative subset inequality
and the entire odd-e Fourier character projector; no complex
signed-subsums, no estimated φ(2|k|), no artificial e/n gates.
The target subset may be the exact recovered B509 physical event
complement, but it is never assumed to have small signed mass.
This reduces the source ghost tail debt to the *actual* individual
B633 pair-mass estimate, not the absolute signed Eq4.17 sum. -/
theorem parity_eventually_original_positive_sigma_ghost_mass_le_real_chi_full_pair_mass434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 Z : ℝ) (signed : Bool) (N : Finset ℕ)
        (physical : (Σ z : ℕ, Σ mp : ℕ, ℕ) → Prop),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i =>
        parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let Wproj : I → ℂ := fun i => g i * (A i*alpha i.2.2*star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
         then (1:ℂ) else 0))
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      (∑i∈s.filter (fun i => ¬physical i), ‖Wproj i‖) ≤
        ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
          (∑i∈s, ‖Wchi chi i‖) := by
  filter_upwards [parity_eventually_original_positive_sigma_projected_B633_mass_le_real_chi_pair_mass434
      S beta gamma Ck hS hbeta hgamma] with L hFull
  refine ⟨hFull.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 Z signed N physical
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Wproj : I → ℂ := fun i => g i * (A i*alpha i.2.2*star (alpha i.2.1)*
    (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
     then (1:ℂ) else 0))
  have hMass := hFull.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 Z signed N
  change (∑i∈s, ‖Wproj i‖) ≤ _ at hMass
  change (∑i∈s.filter (fun i=>¬physical i),‖Wproj i‖) ≤ _
  have hSub : s.filter (fun i=>¬physical i) ⊆ s := Finset.filter_subset _ _
  exact (Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun i hi hnot => norm_nonneg (Wproj i))).trans hMass
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPrimeRestAbsoluteMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Literal Parity(4.16) original H0 reserved-prime REST is an absolute
finite prime-divisor sum, with no cancellation assumption: whenever
the actual native skipped-Q residual has coefficients ≤1, the norm
of the unrestricted prime-slot remainder is bounded by τ(u).
The source interval [lo,hi], real sigma, all prime multiplicities
and original 1/φ character normalization are unchanged. -/
theorem parity_original_B633_prime_rest_absolute_tau434
    (lo hi : ℕ) (sigma : ℝ) (residual : ℕ → ℂ)
    (hres : ∀ t, ‖residual t‖≤1) (u : ℕ) :
    ‖b633PrimeRest434 lo hi sigma residual u‖ ≤
      (u.divisors.card : ℝ) := by
  unfold b633PrimeRest434
  calc
    _ ≤ ∑ p ∈ u.divisors,
        ‖if p.Prime ∧ p ∈ Finset.Icc lo hi then
          imaginaryPower p sigma * residual (u/p) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ u.divisors, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : p.Prime ∧ p ∈ Finset.Icc lo hi
      · rw [if_pos h, norm_mul,
            b656_imaginary_power_norm434 p h.1.pos sigma, one_mul]
        exact hres (u/p)
      · simp only [Finset.mem_Icc] at h
        simp only [Finset.mem_Icc]
        simp [h]
    _ = (u.divisors.card : ℝ) := by simp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPairAbsoluteNorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Actual ONE ORIGINAL Parity(4.16) two-prime-slot summand:
the absolute coefficient mass is bounded by the product of the
TWO ORIGINAL residual-prime divisor counts and actual W1(v)W1(v').
The α and residual sequences are bounded by one, the Dirichlet
character (2|k|) has norm ≤1, all FIVE real Mellin phases have
modulus one at their true positive arguments, and both actual
signed epsilon factors have modulus one. This does not bound a
signed cofactor sum by the absolute value of its total. -/
theorem parity_original_historical_true_B633_pair_absolute_norm434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q)
    (lo hi m mp z zp : ℕ)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hv : 0 < z/mp) (hvp : 0 < zp/m)
    (ha : ∀ t, ‖alpha t‖≤1)
    (hr : ∀ t, ‖residual t‖≤1) :
    ‖parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖ ≤
    ((sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z/mp)).divisors.card:ℝ) *
    ((sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp/m)).divisors.card:ℝ) *
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (z/mp) *
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (zp/m) := by
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  let v := z/mp
  let vp := zp/m
  have hM := b656_imaginary_power_norm434 m hm xi1
  have hMp := b656_imaginary_power_norm434 mp hmp xi2
  have hZ := b656_imaginary_power_norm434 z hz xi3
  have hV := b656_imaginary_power_norm434 v hv rho
  have hVp := b656_imaginary_power_norm434 vp hvp (-rho)
  have hC1 := DirichletCharacter.norm_le_one chi (mp:ZMod q)
  have hC2 := DirichletCharacter.norm_le_one chi (m:ZMod q)
  have hR1 := parity_original_B633_prime_rest_absolute_tau434
      lo hi 0 residual hr (sourceOriginalOrdinaryPart Pall v)
  have hR2 := parity_original_B633_prime_rest_absolute_tau434
      lo hi 0 residual hr (sourceOriginalOrdinaryPart Pall vp)
  have hSign := parity_original_eq417_signed_pair_abs_one434 L signed v vp
  have hMark := parity_original_eq417_marked_pair_norm434 L v vp
  have hW1 := source_original_W1_nonneg P v
  have hW2 := source_original_W1_nonneg P vp
  have hR1p : 0≤((sourceOriginalOrdinaryPart Pall v).divisors.card:ℝ) := Nat.cast_nonneg _
  have hR2p : 0≤((sourceOriginalOrdinaryPart Pall vp).divisors.card:ℝ) := Nat.cast_nonneg _
  have hBase : ‖parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖ =
      (‖alpha m‖*‖alpha mp‖*‖chi (mp:ZMod q)‖*‖chi (m:ZMod q)‖)*
      (‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall v)‖*
       ‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall vp)‖)*
      (sourceOriginalW1 P v*sourceOriginalW1 P vp) := by
    dsimp [v,vp] at hV hVp hSign hMark
    unfold parityOriginalHistoricalB633PhysicalPairTerm434
    simp only [norm_mul, norm_star, hM, hMp, hZ]
    rw [hV,hVp,hSign,hMark]
    dsimp [P,Pall,v,vp]
    ring
  rw [hBase]
  have hA : ‖alpha m‖*‖alpha mp‖*‖chi (mp:ZMod q)‖*‖chi (m:ZMod q)‖≤1 := by
    have h1 := mul_le_mul (ha m) (ha mp) (norm_nonneg _) zero_le_one
    have h2 := mul_le_mul hC1 hC2 (norm_nonneg _) zero_le_one
    nlinarith [mul_nonneg (norm_nonneg (alpha m)) (norm_nonneg (alpha mp)),
      mul_nonneg (norm_nonneg (chi (mp:ZMod q))) (norm_nonneg (chi (m:ZMod q)))]
  have hR : ‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall v)‖*
       ‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall vp)‖ ≤
      ((sourceOriginalOrdinaryPart Pall v).divisors.card:ℝ)*
      ((sourceOriginalOrdinaryPart Pall vp).divisors.card:ℝ) :=
        mul_le_mul hR1 hR2 (norm_nonneg _) hR1p
  have hFirst : (‖alpha m‖*‖alpha mp‖*‖chi (mp:ZMod q)‖*‖chi (m:ZMod q)‖)*
      (‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall v)‖*
       ‖b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall vp)‖) ≤
      ((sourceOriginalOrdinaryPart Pall v).divisors.card:ℝ)*
      ((sourceOriginalOrdinaryPart Pall vp).divisors.card:ℝ) := by
    have hh := mul_le_mul hA hR (by positivity) (by positivity)
    nlinarith [mul_nonneg (norm_nonneg (alpha m)) (norm_nonneg (alpha mp)),
      mul_nonneg (norm_nonneg (chi (mp:ZMod q))) (norm_nonneg (chi (m:ZMod q)))]
  have hh := mul_le_mul_of_nonneg_right hFirst (mul_nonneg hW1 hW2)
  dsimp [P,Pall,v,vp] at hh ⊢
  nlinarith [hh]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqCofactorTauGeometry -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- On a genuine positive Parity(4.16) endpoint z, the P-ordinary
part divides z and therefore has no more divisors than z.
No P-free e gate or rough-support assumption is involved. -/
theorem parity_original_B633_ordinary_tau_le_endpoint434
    (P : Finset ℕ) (z : ℕ) (hz : 0 < z) :
    ((sourceOriginalOrdinaryPart P z).divisors.card:ℝ) ≤
      (z.divisors.card:ℝ) := by
  have hDiv := source_ordinary_part_dvd P z hz.ne'
  have hSub := Nat.divisors_subset_of_dvd hz.ne' hDiv
  exact_mod_cast Finset.card_le_card hSub

/-- For every original unrestricted Parity(4.16) cofactor divisor
d | ordinary_P(z), the full residual prime-slot argument
ordinary_P(z/d) has at most τ(z) divisors. This holds before
any source η_e,η_n support and preserves all prime multiplicities.
Also z/d is automatically a positive actual integer. -/
theorem parity_original_B633_ordinary_quotient_tau_le_endpoint434
    (P : Finset ℕ) (z d : ℕ)
    (hz : 0 < z) (hd : 0 < d)
    (hDiv : d∣sourceOriginalOrdinaryPart P z) :
    0 < z/d ∧
      ((sourceOriginalOrdinaryPart P (z/d)).divisors.card:ℝ) ≤
      (z.divisors.card:ℝ) := by
  have hOrdDiv : sourceOriginalOrdinaryPart P z∣z :=
    source_ordinary_part_dvd P z hz.ne'
  have hdz : d∣z := dvd_trans hDiv hOrdDiv
  have hv : 0 < z/d := Nat.div_pos (Nat.le_of_dvd hz hdz) hd
  have hfact : d*(z/d)=z := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdz
  have hqDiv : z/d∣z := by
    refine ⟨d,?_⟩
    simpa only [mul_comm] using hfact.symm
  have hrv : sourceOriginalOrdinaryPart P (z/d)∣z/d :=
    source_ordinary_part_dvd P (z/d) hv.ne'
  have hSub := Nat.divisors_subset_of_dvd hz.ne' (dvd_trans hrv hqDiv)
  exact ⟨hv, by exact_mod_cast Finset.card_le_card hSub⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqPairTauMajorant -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- For every original positive Parity (4.17) z,z+2k and EACH
actual P-ordinary cofactor-divisor pair (m',m), the literal
B509 prime-slot term is at most τ(z)τ(z+2k) times both original
pointwise W1 factors. The source α and B509 skipped residual
unit bounds are genuine native arithmetic hypotheses, discharged
for the actual fine coefficient and original source separately.
This is a POSITIVE termwise estimate, not a signed correlation. -/
theorem parity_original_B633_individual_cofactor_tau_majorant434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi m mp z zp : ℕ) (hz : 0 < z) (hzp : 0 < zp)
    (hmp : mp∈(sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors)
    (hm : m∈(sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp).divisors)
    (ha : ∀t, ‖alpha t‖≤1) (hr : ∀t, ‖residual t‖≤1)
    (hW : ∀t, sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) t ≤
       L^parityOriginalW1PolylogExponent434) (hL : 0 < L) :
    ‖parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖ ≤
    (z.divisors.card:ℝ)* (zp.divisors.card:ℝ) *
       L^(2*parityOriginalW1PolylogExponent434) := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hmpPos : 0 < mp := Nat.pos_of_mem_divisors hmp
  have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
  have hMp := parity_original_B633_ordinary_quotient_tau_le_endpoint434
    P z mp hz hmpPos (Nat.mem_divisors.mp hmp).1
  have hM := parity_original_B633_ordinary_quotient_tau_le_endpoint434
    P zp m hzp hmPos (Nat.mem_divisors.mp hm).1
  have hPair := parity_original_historical_true_B633_pair_absolute_norm434
    L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
    m mp z zp hmPos hmpPos hz hzp hMp.1 hM.1 ha hr
  let r := ((sourceOriginalOrdinaryPart P (z/mp)).divisors.card:ℝ)
  let s := ((sourceOriginalOrdinaryPart P (zp/m)).divisors.card:ℝ)
  let A := (z.divisors.card:ℝ)
  let B := (zp.divisors.card:ℝ)
  let C := L^parityOriginalW1PolylogExponent434
  let wa := sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (z/mp)
  let wb := sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (zp/m)
  have hCard : r*s ≤ A*B :=
    mul_le_mul hMp.2 hM.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hWa : 0 ≤ wa := source_original_W1_nonneg _ _
  have hWb : 0 ≤ wb := source_original_W1_nonneg _ _
  have hWprod : wa*wb ≤ C*C :=
    mul_le_mul (hW _) (hW _) hWb (Real.rpow_nonneg hL.le _)
  have hProd := mul_le_mul hCard hWprod
    (mul_nonneg hWa hWb) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hPow : C*C=L^(2*parityOriginalW1PolylogExponent434) := by
    dsimp only [C]
    rw [←Real.rpow_add hL]
    congr 1
    ring
  change ‖parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖ ≤
      A*B*L^(2*parityOriginalW1PolylogExponent434)
  calc
    _ ≤ r*s*wa*wb := hPair
    _ = (r*s)*(wa*wb) := by ring
    _ ≤ (A*B)*(C*C) := hProd
    _ = _ := by rw [hPow]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullDoublePairMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1900000

/-- Absolute mass of the entire genuine Parity(4.16) original DOUBLE
ordinary-divisor cofactor expansion at a fixed shifted pair of
positive z,zp. Each of the two source cofactor divisor sets has at
most τ(z) or τ(zp) members, and each literal B509/α/χ/W1/ε
pair has norm at most τ(z)τ(zp)L^(2CW1). Thus the complete
SUM OF NORMS, not norm of the signed core sum, is bounded by
L^(2CW1) τ(z)^2 τ(zp)^2. All multiplicities remain literal. -/
theorem parity_original_B633_full_double_pair_absolute_fourth_tau434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi z zp : ℕ)
    (hz : 0 < z) (hzp : 0 < zp)
    (ha : ∀t, ‖alpha t‖≤1) (hr : ∀t, ‖residual t‖≤1)
    (hW : ∀t, sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) t ≤
       L^parityOriginalW1PolylogExponent434) (hL : 0 < L) :
    (∑ mp∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp).divisors,
        ‖parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖) ≤
    L^(2*parityOriginalW1PolylogExponent434) *
      (z.divisors.card:ℝ)^2 * (zp.divisors.card:ℝ)^2 := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let D := (sourceOriginalOrdinaryPart P z).divisors
  let Dp := (sourceOriginalOrdinaryPart P zp).divisors
  let A := (z.divisors.card:ℝ)
  let B := (zp.divisors.card:ℝ)
  let R := L^(2*parityOriginalW1PolylogExponent434)
  have hBound (mp : ℕ) (hmp : mp∈D) (m : ℕ) (hm : m∈Dp) :
      ‖parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖ ≤
      A*B*R :=
    parity_original_B633_individual_cofactor_tau_majorant434
      L rho xi1 xi2 xi3 signed alpha residual q chi
      lo hi m mp z zp hz hzp hmp hm ha hr hW hL
  have hSum : (∑mp∈D,∑m∈Dp,
        ‖parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖) ≤
      ∑mp∈D,∑_m∈Dp,A*B*R := by
    apply Finset.sum_le_sum
    intro mp hmp
    apply Finset.sum_le_sum
    intro m hm
    exact hBound mp hmp m hm
  have hCountZ : (D.card:ℝ) ≤ A :=
    parity_original_B633_ordinary_tau_le_endpoint434 P z hz
  have hCountZp : (Dp.card:ℝ) ≤ B :=
    parity_original_B633_ordinary_tau_le_endpoint434 P zp hzp
  have hCount : (D.card:ℝ)*(Dp.card:ℝ) ≤ A*B :=
    mul_le_mul hCountZ hCountZp (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hBR : 0≤A*B*R := by dsimp [A,B,R]; positivity
  have hTotals : (∑mp∈D,∑_m∈Dp,A*B*R) =
      ((D.card:ℝ)*(Dp.card:ℝ))*(A*B*R) := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  change (∑mp∈D,∑m∈Dp,
      ‖parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha residual q chi lo hi m mp z zp‖) ≤
      R*A^2*B^2
  calc
    _ ≤ ∑mp∈D,∑_m∈Dp,A*B*R := hSum
    _ = ((D.card:ℝ)*(Dp.card:ℝ))*(A*B*R) := hTotals
    _ ≤ (A*B)*(A*B*R) := mul_le_mul_of_nonneg_right hCount hBR
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFullSigmaAbsoluteMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- Complete ORIGINAL Parity(4.16)-(4.17) unrestricted absolute
B633 PAIR mass, not the norm of a signed or cofactor-contracted
correlation. All cofactor prime-slot B509 H0 atoms and two W1/ε
factors remain literal, with correct positive shifted z+2k.
For the genuine C∞ ψ_Z support and |2k|≤Z/128, the entire
SUM OF INDIVIDUAL PAIR NORMS has the native translated fourth
divisor moment bound Cψ L^(2CW1) Y(1+logY)^15, Y=ceil65Z.
Neither the number of characters, m,m',z nor e/n is paid
separately; they occur inside the proven pair and divisor moment.
Hypotheses α,c_r unit are arithmetic and are independently
proved for the genuine B629/B509 source by native B656. -/
theorem parity_original_B633_unrestricted_full_sigma_pair_absolute_mass434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (k : ℤ) (Z : ℝ) (psi : ℝ → ℂ) (N : Finset ℕ)
    (hL : 0 < L) (hZ : 0 < Z)
    (hk : |((2*k:ℤ):ℝ)| ≤ Z/128)
    (hSupport : ∀t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64)
    (Cpsi : ℝ) (hCpsi : 0≤Cpsi) (hPsi : ∀t, ‖psi t‖≤Cpsi)
    (ha : ∀t, ‖alpha t‖≤1) (hr : ∀t, ‖residual t‖≤1)
    (hW : ∀t,sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) t ≤
      L^parityOriginalW1PolylogExponent434) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let s := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
    let Y := Nat.ceil (65*Z)
    (∑z∈s,
      ∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z) * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)‖) ≤
      Cpsi * L^(2*parityOriginalW1PolylogExponent434) *
        (Y:ℝ) * (1+Real.log (Y:ℝ))^15 := by
  dsimp only
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let s := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
  let Y := Nat.ceil (65*Z)
  let C := L^(2*parityOriginalW1PolylogExponent434)
  let a : ℕ → ℝ := fun z =>
    (z.divisors.card:ℝ)^2 * ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2)
  have hC : 0≤C := Real.rpow_nonneg hL.le _
  have hEach (z : ℕ) (hz : z∈s) :
      (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
       ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z) * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)‖) ≤
      ‖psi ((z:ℝ)/Z)‖ * C * a z := by
    have hh := (Finset.mem_filter.mp hz).2
    have hShift := parity_harmonic_cutoff_shift_support434
      Z hZ (2*k) hk psi hSupport z hh.2
    have hzPos : 0<z := by
      have hreal : (0:ℝ)<(z:ℝ) :=
        (div_pos hZ (by norm_num)).trans_le hShift.2.2.2
      exact_mod_cast hreal
    have hzpPos : 0 < (((z:ℤ)+2*k).toNat) := by omega
    have hDouble := parity_original_B633_full_double_pair_absolute_fourth_tau434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
      z (((z:ℤ)+2*k).toNat) hzPos hzpPos ha hr hW hL
    have hPull : (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z) * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)‖) =
      ‖psi ((z:ℝ)/Z)‖ *
        (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
         ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
          ‖parityOriginalHistoricalB633PhysicalPairTerm434
            L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
            m mp z (((z:ℤ)+2*k).toNat)‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mp hmp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [norm_mul]
    rw [hPull]
    have hψ := norm_nonneg (psi ((z:ℝ)/Z))
    have hMul := mul_le_mul_of_nonneg_left hDouble hψ
    dsimp only [C,a,P] at hMul ⊢
    nlinarith [hMul]
  have hPrime : (∑z∈s, a z) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 :=
    parity_original_historical_unrestricted_417_shifted_tau_pair_mass434
      k Z psi N hZ hk hSupport
  have hTerm (z : ℕ) (hz : z∈s) :
      (∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
       ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z) * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)‖) ≤
        Cpsi*C*a z := by
    have h0 := hEach z hz
    have hPsi0 := hPsi ((z:ℝ)/Z)
    have hapos : 0≤a z := by dsimp [a];positivity
    calc
      _ ≤ ‖psi ((z:ℝ)/Z)‖*C*a z := h0
      _ ≤ Cpsi*C*a z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hPsi0 hC) hapos
  have hSum := Finset.sum_le_sum hTerm
  have hSimpl : (∑z∈s,Cpsi*C*a z) = Cpsi*C*(∑z∈s,a z) := by
    rw [Finset.mul_sum]
  have hCC : 0≤Cpsi*C := mul_nonneg hCpsi hC
  change (∑z∈s,
      ∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z) * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
          m mp z (((z:ℤ)+2*k).toNat)‖) ≤
    Cpsi*C*(Y:ℝ)*(1+Real.log (Y:ℝ))^15
  calc
    _ ≤ ∑z∈s,Cpsi*C*a z := hSum
    _ = Cpsi*C*(∑z∈s,a z) := hSimpl
    _ ≤ Cpsi*C*((Y:ℝ)*(1+Real.log (Y:ℝ))^15) :=
      mul_le_mul_of_nonneg_left hPrime hCC
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSigmaAbsoluteMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- UNCONDITIONAL actual Parity(4.16)-(4.17) original B633 Σ absolute
pair-mass at fixed k,Z,χ with the true b629 canonical fine alpha,
the native full 20-slot moving Q skipped residual c_r, genuine
reserved Q prime H0 and the C∞ dyadic ψ. Actual coefficient
bounds |α_m|≤1 and |c_r|≤1 are imported AS PROVED from native
B656; actual uniform W1 is imported AS PROVED from source P group.
All original source marks and parity, repeated prime factors and
signed shift 2k remain unchanged. No upper exp(2L) cutoff is
needed for this *pairwise* positive bound; no spectral saving.
No #χ, #m, #m', #e, or #z multiplier appears. -/
theorem parity_eventually_original_actual_B633_full_sigma_positive_pair_mass434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      Real.exp (beta*L)≤(l:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (K : Finset ℕ) (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 Z : ℝ) (signed : Bool) (N : Finset ℕ),
      0<Z → |((2*k:ℤ):ℝ)|≤Z/128 →
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u)
        (2*k.natAbs) chi 0 0
      let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let psi := parityOriginalHistoricalDyadicSmoothPsi434
      let s := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
      let Y := Nat.ceil (65*Z)
      (∑z∈s,
       ∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
       ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
         ‖psi ((z:ℝ)/Z)*parityOriginalHistoricalB633PhysicalPairTerm434
           L rho xi1 xi2 xi3 signed F.alpha F.residual
           (2*k.natAbs) chi F.lo F.hi m mp z (((z:ℤ)+2*k).toNat)‖) ≤
        L^(2*parityOriginalW1PolylogExponent434) *
          (Y:ℝ)*(1+Real.log (Y:ℝ))^15 := by
  filter_upwards [b656_actual_fine_native_and_parity_inputs434
      S beta gamma hS hbeta hgamma,
    parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_ge_atTop (1:ℝ)] with L hNative hW hL
  refine ⟨hL,?_⟩
  intro prime l u hFine d band slot δ ξ K k chi
    rho xi1 xi2 xi3 Z signed N hZ hk
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u)
    (2*k.natAbs) chi 0 0
  have hCoeffs : B656UnitRoughPrimeCore434 L F :=
    (hNative.2 prime l u hFine 20 d (by norm_num) band slot δ ξ
      K (2*k.natAbs) chi 0 0).1
  have hMass := parity_original_B633_unrestricted_full_sigma_pair_absolute_mass434
    L rho xi1 xi2 xi3 signed F.alpha F.residual (2*k.natAbs) chi
    F.lo F.hi k Z parityOriginalHistoricalDyadicSmoothPsi434 N
    (by linarith) hZ hk
    parity_original_historical_dyadic_psi_Parity417_support434
    1 (by norm_num) parity_original_historical_explicit_smooth_dyadic_psi_norm_le_one434
    hCoeffs.1 hCoeffs.2.1 hW
  simpa only [one_mul] using hMass
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSigmaPsiNormReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Exact FINITE positive unrestricted Parity(4.17) P-divisor Sigma
reindex for the actual absolute ψ-weighted B633 pair mass.
The source finite z-domain may be arbitrary: the true ψ=0 and
z+2k≤0 terms are removed by exact ZERO equalities, not by a
hypothetical signed-subsum inequality. No new positivity, source
physical e/n gate or fake multiplicity is introduced. -/
theorem parity_original_positive_sigma_psi_absolute_mass_reindex434
    (L : ℝ) (k : ℤ) (Z : ℝ) (psi : ℝ → ℂ)
    (N : Finset ℕ) (A : ℕ → ℕ → ℕ → ℂ) :
    (∑i∈parityOriginalHistoricalActualB633PositiveSigma434 L k N,
      ‖psi ((i.1:ℝ)/Z)*A i.1 i.2.1 i.2.2‖) =
    ∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N,
      ∑mp∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
          (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z)*A z mp m‖ := by
  classical
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let F (z : ℕ) :=
    (sourceOriginalOrdinaryPart P z).divisors.sigma
      (fun _mp => (sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors)
  change (∑i∈(N.sigma F).filter (fun i => 0<(i.1:ℤ)+2*k),
       ‖psi ((i.1:ℝ)/Z)*A i.1 i.2.1 i.2.2‖) =
    ∑z∈N.filter (fun z : ℕ => (0:ℤ)<(z:ℤ)+2*k ∧ psi ((z:ℝ)/Z)≠0),
      ∑mp∈(sourceOriginalOrdinaryPart P z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart P (((z:ℤ)+2*k).toNat)).divisors,
        ‖psi ((z:ℝ)/Z)*A z mp m‖
  rw [Finset.sum_filter,Finset.sum_sigma,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp [F]
  rw [Finset.sum_sigma]
  by_cases hzp : 0<(z:ℤ)+2*k
  · by_cases hPsi : psi ((z:ℝ)/Z)=0
    · simp [hzp,hPsi]
    · simp [hzp,hPsi]
  · simp [hzp]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSigmaGhostPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- UNCONDITIONAL source original Parity(4.16)-(4.17) POSITIVE ghost
cofactor mass at fixed signed k,Z, beyond all real B509 physical
(e,n) filters. The entire complete character projector is applied
BEFORE taking absolute values, and its true coefficient ℓ1 mass
≤1 removes any #characters cost. Every individual original Q/B509
prime-slot H0 term is controlled via its genuine residual |c_r|≤1;
full double cofactor divisor mass uses the translated FOURTH divisor
moment with BOTH P-W1 factors, not a false bound on signed sub-sums.
This proves Σ_ghost |ψ_Z B633_projected_pair| ≤ L^(2CW1)
ceil(65Z)(1+logceil(65Z))^15 uniformly over ANY physical mask.
It does not yet identify the entire original physical B-prime source
with the Σ image or sum the outer k/Z/branch Fourier budgets. -/
theorem parity_eventually_original_B633_any_sigma_ghost_positive_mass_polylog434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 Z : ℝ) (signed : Bool) (N : Finset ℕ),
      0<Z → |((2*k:ℤ):ℝ)|≤Z/128 →
      ∀ (physical : (Σ z : ℕ, Σ mp : ℕ, ℕ) → Prop),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i =>
        parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let Wproj : I → ℂ := fun i => g i * (A i*alpha i.2.2*star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
         then (1:ℂ) else 0))
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      (∑i∈s.filter (fun i => ¬physical i), ‖Wproj i‖) ≤
        L^(2*parityOriginalW1PolylogExponent434)*
          ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
  filter_upwards [parity_eventually_original_positive_sigma_ghost_mass_le_real_chi_full_pair_mass434
      S beta gamma Ck hS hbeta hgamma,
    b629_actual_fine_coefficient_and_rough_support434
      S beta gamma hS hbeta hgamma,
    parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_ge_atTop (1:ℝ)] with L hGhostL hCoeff hWL hL
  refine ⟨hL,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 Z signed N hZ hkZ physical
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Wproj : I → ℂ := fun i => g i*(A i*alpha i.2.2*star (alpha i.2.1)*
    (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
     then (1:ℂ) else 0))
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    g i * parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let Y := Nat.ceil (65*Z)
  let M : ℝ := L^(2*parityOriginalW1PolylogExponent434)*
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15
  have hAlpha : ∀t,‖alpha t‖≤1 := by
    intro t
    by_cases ht : t∈K
    · simpa only [alpha,restrictSequence,ht,ite_true] using
        (hCoeff prime l u hlow t).1
    · simp [alpha,restrictSequence,ht]
  have hLpos : 0<L := by linarith
  have hOne (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      (∑i∈s,‖Wchi chi i‖) ≤ M := by
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    have hR : ∀ t,‖F.residual t‖≤1 :=
      source_native_residual_norm_le_one 20 d L (by norm_num) hLpos
        band slot δ ξ K alpha (2*k.natAbs) chi 0 0
    have hFull := parity_original_B633_unrestricted_full_sigma_pair_absolute_mass434
      L rho xi1 xi2 xi3 signed alpha F.residual (2*k.natAbs) chi
      F.lo F.hi k Z parityOriginalHistoricalDyadicSmoothPsi434 N
      hLpos hZ hkZ
      parity_original_historical_dyadic_psi_Parity417_support434
      1 (by norm_num) parity_original_historical_explicit_smooth_dyadic_psi_norm_le_one434
      hAlpha hR hWL
    have hReindex := parity_original_positive_sigma_psi_absolute_mass_reindex434
      L k Z parityOriginalHistoricalDyadicSmoothPsi434 N
      (fun z mp m => parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual (2*k.natAbs)
        chi F.lo F.hi m mp z (((z:ℤ)+2*k).toNat))
    change (∑i∈s, ‖Wchi chi i‖) =
      ∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z
        parityOriginalHistoricalDyadicSmoothPsi434 N,
      ∑mp∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z).divisors,
      ∑m∈(sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
          (((z:ℤ)+2*k).toNat)).divisors,
      ‖parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/Z)*
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi m mp z (((z:ℤ)+2*k).toNat)‖
      at hReindex
    rw [hReindex]
    simpa only [one_mul] using hFull
  have hGhost := hGhostL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 Z signed N physical
  change (∑i∈s.filter (fun i=>¬physical i), ‖Wproj i‖) ≤
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
      (∑i∈s,‖Wchi chi i‖) at hGhost
  have hM : 0≤M := by
    have hNonneg : (0:ℝ)≤∑i∈s,‖Wchi (1:DirichletCharacter ℂ (2*k.natAbs)) i‖ :=
      Finset.sum_nonneg (fun i hi => norm_nonneg _)
    exact hNonneg.trans (hOne 1)
  change (∑i∈s.filter (fun i=>¬physical i), ‖Wproj i‖) ≤ M
  calc
    _ ≤ ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ *
      (∑i∈s,‖Wchi chi i‖) := hGhost
    _ ≤ ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ * M := by
        apply Finset.sum_le_sum
        intro chi hchi
        exact mul_le_mul_of_nonneg_left (hOne chi) (norm_nonneg _)
    _ = M*(∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) := by
        rw [←Finset.sum_mul]
        ring
    _ ≤ M*1 := mul_le_mul_of_nonneg_left
      (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = _ := mul_one M
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSigmaGhostQuantifiedBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- Source original 20-slot B633 full ψ-weighted physical low-frequency
ball bound by the ACTUAL full signed (4.17) χ-summed Fourier integral
plus an EXPLICIT polynomial positive ghost tail. The genuine ghost
mass is proved from actual residual c_r, double ordinary-P divisors,
W1 and the translated fourth divisor moment. The full χ-sum is
formed before imposing the B509 source n/e physical mask and before
norms. No per-character positivity or complex-subsum assumptions.
This is a fixed-k,Z result; outer type II families remain open. -/
theorem parity_eventually_original_actual_B633_psi_ball_le_eq417_plus_proven_polylog_ghost434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ (N : Finset ℕ), (∀ z∈N,0<z) →
        |((2*k:ℤ):ℝ)|≤Z/128 →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
      let m : I → ℕ := fun i => i.2.2
      let mp : I → ℕ := fun i => i.2.1
      let z : I → ℕ := fun i => i.1
      let zp : I → ℕ := fun i => (((i.1:ℤ)+2*k).toNat)
      let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let good : I → Prop := fun i => m i∈K ∧ mp i∈K ∧ m i≠mp i
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        (m i) (mp i) (z i) (zp i)
      let Wproj : I → ℂ := fun i => g i*A i*alpha (m i)*star (alpha (mp i))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
        let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
        g i * parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let physical : I → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0 < en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter physical) Wproj t f ζ‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                  (2*k.natAbs) chi 0 0
               parityOriginalHistoricalActualB633FullFourierCofactor434
                 L rho xi1 xi2 xi3 U Z k N alpha F.residual
                 (2*k.natAbs) chi F.lo F.hi signed
                 parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖ +
      (L^(2*parityOriginalW1PolylogExponent434)*
          ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_actual_B633_positive_sigma_psi_ball_le_original_eq417434
    S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_B633_any_sigma_ghost_positive_mass_polylog434
    S beta gamma Ck hS hbeta hgamma] with L hBallL hGhostL
  refine ⟨hBallL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN hkZ buf a b hSmooth hBufSupport H T hT
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let good : I → Prop := fun i => i.2.2∈K ∧ i.2.1∈K ∧ i.2.2≠i.2.1
  let physical : I → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧
      ∃ n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ (Nat.ceil (6*U*V)) en i.2.2 K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
        parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let g : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Wproj : I → ℂ := fun i => g i*A i*alpha i.2.2*star (alpha i.2.1)*
    (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
     then (1:ℂ) else 0)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  let M : ℝ := L^(2*parityOriginalW1PolylogExponent434)*
    ((Nat.ceil (65*Z):ℕ):ℝ)*
    (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15
  let B : ℝ := parityOriginal3DSourceMomentFiniteBudget434 H f/T^H
  have hBall := hBallL.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN buf a b hSmooth hBufSupport H T hT
  have hMass := hGhostL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 Z signed N hZ hkZ
    (fun i => physical i)
  have hMass0 : parityOriginal3DPhysicalFiniteCoefficientMass434
      ((s.filter good).filter (fun i => ¬physical i)) Wproj ≤ M := by
    have hSub : (s.filter good).filter (fun i => ¬physical i) ⊆
        s.filter (fun i => ¬physical i) := by
      intro i hi
      obtain ⟨hgood,hnon⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hgood).1,hnon⟩
    have hSubset := Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun i hi hnot => norm_nonneg (Wproj i))
    have hEq : (∑i∈s.filter (fun i => ¬physical i), ‖Wproj i‖) =
        ∑i∈s.filter (fun i => ¬physical i),
          ‖g i*(A i*alpha i.2.2*star (alpha i.2.1)*
            (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
              then (1:ℂ) else 0))‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ring
    change (∑i∈s.filter (fun i => ¬physical i),
        ‖g i*(A i*alpha i.2.2*star (alpha i.2.1)*
          (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
            then (1:ℂ) else 0))‖) ≤ M at hMass
    rw [←hEq] at hMass
    exact hSubset.trans hMass
  have hB : 0≤B := by
    unfold B parityOriginal3DSourceMomentFiniteBudget434
      parityOriginal3DSourceFiniteSeminormBudget434
    have hC := parity_original_3d_source_geometric_constant_nonneg434
    positivity
  dsimp only at hBall ⊢
  exact hBall.trans (by
    have hh := add_le_add_left (mul_le_mul_of_nonneg_right hMass0 hB)
      (‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
              (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                (2*k.natAbs) chi 0 0
               parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha F.residual
                (2*k.natAbs) chi F.lo F.hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖)
    simpa only [add_comm] using hh)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedSourceSigmaForward -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- ACTUAL ORIGINAL full-odd-e ungated post-Cauchy B509 source
(e,n,m,m') maps into the literal FULL UNRESTRICTED Parity(4.17)
positive-shift Sigma index (z,m',m). This is a forward embedding
with NO P-free restriction on e and no invented source cutoff:
source v=(mn-2)/e, z=m'v, z+2k=mv', and both cofactors divide
the two original P-ordinary parts. Real P-freeness of m,m'
comes from native exp(sqrt L)-roughness and the genuine group
prime upper bound. The arbitrary finite N only needs to CONTAIN
the literal canonical z, which is precisely the original index
membership in a finite z-sum, not an artificial hard source gate.
This theorem does not assert the full inverse or complex signed
sum equality. -/
theorem parity_original_ungated_true_source_in_positive_B633_sigma434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hne : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hRoughMp : sourceD20Rough (Real.exp (Real.sqrt L)) mp)
    (N : Finset ℕ)
    (hZmem : parityOriginalHistoricalCanonicalZ434 e m mp n∈N) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    k≠0 ∧ 0 < z ∧
      ((⟨z,⟨mp,m⟩⟩ : Σ z : ℕ, Σ mp : ℕ, ℕ) ∈
        parityOriginalHistoricalActualB633PositiveSigma434 L k N) := by
  dsimp only
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  obtain ⟨v,vp,vs,vps,hv,hvp,hMN,hMpN,hvs,hvps,hSourceV,hSourceVp⟩ :=
    parity_original_historical_ungated_physical_valid_n_real_endpoints434
      d L band slot δ Y e m mp n he.pos hValid
  have hm : 0 < m := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hup).2.1
  have hP : ∀g p,p∈sourceOriginalPAllActualBands 20 L g →
      p.Prime ∧ (p:ℝ)≤Real.exp (Real.sqrt L) :=
    parity_original_actual_full_P_prime_rough_cap434 L hL
  have hMFree : ∀p∈P,¬p∣m :=
    parity_original_actual_rough_prime_free_on_P434
      (sourceOriginalPAllActualBands 20 L) (Real.exp (Real.sqrt L))
      m hRoughM (fun g p hp => (hP g p hp).1)
      (fun g p hp => (hP g p hp).2)
  have hMpFree : ∀p∈P,¬p∣mp :=
    parity_original_actual_rough_prime_free_on_P434
      (sourceOriginalPAllActualBands 20 L) (Real.exp (Real.sqrt L))
      mp hRoughMp (fun g p hp => (hP g p hp).1)
      (fun g p hp => (hP g p hp).2)
  obtain ⟨k',hk',hDet,hShift,hOrdZ,hOrdZp,hDivMp,hDivM⟩ :=
    parity_original_historical_ungated_two_core_forward434
      P e n m mp v vp he hne hm hmp hv hvp
      hMFree hMpFree hMN hMpN
  have hK : k=k' :=
    parity_original_historical_physical_k_eq_quotient434
      e m mp he.pos k' hDet
  have hVeq : parityOriginalHistoricalCanonicalV434 e m n=v := by
    unfold parityOriginalHistoricalCanonicalV434
    have hh : m*n-2=e*v := by omega
    rw [hh,Nat.mul_div_cancel_left v he.pos]
  have hZeq : z=mp*v := by
    dsimp [z,parityOriginalHistoricalCanonicalZ434]
    rw [hVeq]
  have hZPos : 0 < z := by rw [hZeq];exact Nat.mul_pos hmp hv
  have hShiftZ : (z:ℤ)+2*k=(m*vp:ℕ) := by
    rw [hZeq,hK]
    exact hShift
  have hZpEq : ((z:ℤ)+2*k).toNat=m*vp := by
    have hh := congrArg Int.toNat hShiftZ
    simpa only [Int.toNat_natCast] using hh
  have hShiftPos : 0<(z:ℤ)+2*k := by
    rw [hShiftZ]
    exact_mod_cast Nat.mul_pos hm hvp
  have hMem : (⟨z,⟨mp,m⟩⟩ : Σ z : ℕ, Σ mp : ℕ, ℕ) ∈
      parityOriginalHistoricalActualB633PositiveSigma434 L k N := by
    unfold parityOriginalHistoricalActualB633PositiveSigma434
      parityOriginalHistoricalActualB633FullSigmaIndex434
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_sigma.mpr
      constructor
      · exact hZmem
      · apply Finset.mem_sigma.mpr
        constructor
        · rw [hZeq]
          exact hDivMp
        · rw [hZpEq]
          exact hDivM
    · exact hShiftPos
  refine ⟨?_,hZPos,hMem⟩
  change k ≠ 0
  rw [hK]
  exact hk'
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedSourceSigmaUnique -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- ORIGINAL CORRECTED ungated full-odd-e source: for a given e,m,m'
and true shifted z, the SOURCE shared integer n is unique on the
actual two-endpoint Q/P/H0 physical support. This is proved from
the literal mn=e v+2, m'n=e v'+2 and z=m'v, without relying on
the old selected-Q Pfree-e carrier or a signed cofactor mass bound. -/
theorem parity_original_ungated_physical_same_e_z_unique_n434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n n' : ℕ) (he : 0 < e)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hValid' : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n')
    (hZ : parityOriginalHistoricalCanonicalZ434 e m mp n =
      parityOriginalHistoricalCanonicalZ434 e m mp n') : n=n' := by
  obtain ⟨v,vp,vs,vps,hv,hvp,hMN,hMpN,_,_,_,_⟩ :=
    parity_original_historical_ungated_physical_valid_n_real_endpoints434
      d L band slot δ Y e m mp n he hValid
  obtain ⟨w,wp,ws,wps,hw,hwp,hMN',hMpN',_,_,_,_⟩ :=
    parity_original_historical_ungated_physical_valid_n_real_endpoints434
      d L band slot δ Y e m mp n' he hValid'
  have hm : 0 < m := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hup).2.1
  have hV : parityOriginalHistoricalCanonicalV434 e m n=v := by
    unfold parityOriginalHistoricalCanonicalV434
    have hnat : m*n-2=e*v := by omega
    rw [hnat,Nat.mul_div_cancel_left v he]
  have hW : parityOriginalHistoricalCanonicalV434 e m n'=w := by
    unfold parityOriginalHistoricalCanonicalV434
    have hnat : m*n'-2=e*w := by omega
    rw [hnat,Nat.mul_div_cancel_left w he]
  have hmul : mp*v=mp*w := by
    unfold parityOriginalHistoricalCanonicalZ434 at hZ
    rwa [hV,hW] at hZ
  have hvEq : v=w := Nat.eq_of_mul_eq_mul_left hmp hmul
  have hmnEq : m*n=m*n' := by
    rw [hMN,hMN',hvEq]
  exact Nat.eq_of_mul_eq_mul_left hm hmnEq

/-- At fixed actual nonzero signed original Parity k and cofactor
m,m' (m≠m'), the odd selected source e is UNIQUE and, if the
canonical z agrees, the corresponding physical shared n is also
UNIQUE. Applies to the NEW full odd-e ungated source, including
original e divisible by group P primes. This prevents any #e/#n
multiplicity when reindexing genuine physical source into the
complete Parity positive (z,m',m) Sigma correlation. -/
theorem parity_original_ungated_physical_fixed_k_z_unique_e_n434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e e' m mp n n' : ℕ) (k : ℤ)
    (he : Odd e) (he' : Odd e') (hNe : m≠mp) (hk : k≠0)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hValid' : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e' m mp n')
    (hK : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hK' : parityOriginalHistoricalOffdiagK434 e' m mp=k)
    (hZ : parityOriginalHistoricalCanonicalZ434 e m mp n =
      parityOriginalHistoricalCanonicalZ434 e' m mp n') :
    e=e' ∧ n=n' := by
  have hDet := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hNe hValid
  have hDet' := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e' m mp n' he' hNe hValid'
  rw [hK] at hDet
  rw [hK'] at hDet'
  have heInt : (e:ℤ)=(e':ℤ) := by
    have hh : (e:ℤ)*k=(e':ℤ)*k := hDet.symm.trans hDet'
    exact mul_right_cancel₀ hk hh
  have heNat : e=e' := by exact_mod_cast heInt
  subst e'
  refine ⟨rfl,?_⟩
  exact parity_original_ungated_physical_same_e_z_unique_n434
    d L band slot δ Y e m mp n n' he.pos hValid hValid' hZ
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedSourceSigmaInjective -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- The genuine all-odd-e source mapping at fixed cofactor m:
   (e,m',n) -> (z=m'*(mn-2)/e,m',m).
No artificial multiplicity quotient or unknown n/χ amplitude. -/
def parityOriginalHistoricalUngatedSourceToSigma434 (m : ℕ)
    (q : ℕ × (ℕ × ℕ)) : Σ z : ℕ, Σ mp : ℕ, ℕ :=
  ⟨parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2,
    ⟨q.2.1,m⟩⟩

/-- ON THE REAL SOURCE all-odd-e ungated h=-2 populated B509
physical event domain, the map (e,m',n)->(z,m',m) is INJECTIVE
once the genuine signed k is fixed and nonzero. The original e,
n and m' are uniquely determined; no hidden #e or #n factor
is generated by finite source-to-B633 reindex. Unlike an index
set comparison this does not assert equality to all unrestricted
Parity4.17 pairs or any signed cancellation estimate. -/
theorem parity_original_ungated_true_source_to_sigma_injective434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (k : ℤ) (hk : k≠0)
    (S : Finset (ℕ × (ℕ × ℕ)))
    (hS : ∀q∈S,
      Odd q.1 ∧ m≠q.2.1 ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
      parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k) :
    Set.InjOn (parityOriginalHistoricalUngatedSourceToSigma434 m)
      (S : Set (ℕ × (ℕ × ℕ))) := by
  intro q hq q' hq' hEq
  rcases q with ⟨e,⟨mp,n⟩⟩
  rcases q' with ⟨e',⟨mp',n'⟩⟩
  dsimp only [parityOriginalHistoricalUngatedSourceToSigma434] at hEq
  have hmp : mp=mp' := by
    have hc := congrArg (fun p : Σ z : ℕ, Σ mp : ℕ, ℕ => p.2.1) hEq
    simpa [parityOriginalHistoricalUngatedSourceToSigma434] using hc
  subst mp'
  obtain ⟨he,hne,hValid,hK⟩ := hS (e, (mp,n)) hq
  obtain ⟨he',hne',hValid',hK'⟩ := hS (e', (mp,n')) hq'
  have hZ : parityOriginalHistoricalCanonicalZ434 e m mp n =
      parityOriginalHistoricalCanonicalZ434 e' m mp n' := by
    have hc := congrArg (fun p : Σ z : ℕ, Σ mp : ℕ, ℕ => p.1) hEq
    simpa [parityOriginalHistoricalUngatedSourceToSigma434] using hc
  obtain ⟨heEq,hnEq⟩ :=
    parity_original_ungated_physical_fixed_k_z_unique_e_n434
      d L band slot δ Y e e' m mp n n' k
      he he' hne hk hValid hValid' hK hK' hZ
  subst e'
  subst n'
  rfl

/-- EXACT original source finite COMPLEX signed reindex, with full
source data (e,m',n), preserving multiplicities exactly ONCE.
The source weights may already include χ(m')/φ(2|k|), eta_e,
eta_n, H0, W1, original epsilon and fixed smooth dyadic ψ.
No positivity or smallness of a selected complex subsum enters. -/
theorem parity_original_ungated_true_source_to_sigma_signed_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (k : ℤ) (hk : k≠0)
    (S : Finset (ℕ × (ℕ × ℕ)))
    (hS : ∀q∈S,
      Odd q.1 ∧ m≠q.2.1 ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
      parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑q∈S, W (parityOriginalHistoricalUngatedSourceToSigma434 m q)) =
    ∑i∈S.image (parityOriginalHistoricalUngatedSourceToSigma434 m), W i := by
  classical
  exact (Finset.sum_image (parity_original_ungated_true_source_to_sigma_injective434
    d L band slot δ Y m k hk S hS)).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedActualSourceSigma -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- LITERAL full-odd e≤2E/n≤3V UNGATED original B509
Parity(4.10) physical source at fixed m and signed k. It is exactly
the all-odd-e source-product e×m'×n filtered by real two-endpoint
h=-2 physical validity and original canonical k; no P-free-e,
selected-Q e, fake n or sharp source z gate is inserted. -/
def parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  ((parityOriginalHistoricalFullOddEEnvelope434 E).product
    ((K.erase m).product (parityOriginalHistoricalFullNEnvelope434 V))).filter
      (fun q => parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
        parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k)

/-- Every member of the exact corrected original finite e×m'×n
source carries literal odd e, distinct physical m', both true
Q/P/B509 endpoint gates and the exact same original k. -/
theorem parity_original_ungated_actual_fixed_m_k_source_legal434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ)
    (q : ℕ × (ℕ × ℕ))
    (hq : q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k) :
    q.1∈parityOriginalHistoricalFullOddEEnvelope434 E ∧
    q.2.1∈K.erase m ∧ q.2.2∈parityOriginalHistoricalFullNEnvelope434 V ∧
    Odd q.1 ∧ m≠q.2.1 ∧
    parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
    parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k := by
  have h := Finset.mem_filter.mp hq
  obtain ⟨he,hmn⟩ := Finset.mem_product.mp h.1
  obtain ⟨hmp,hn⟩ := Finset.mem_product.mp hmn
  exact ⟨he,hmp,hn,(Finset.mem_filter.mp he).2,
    (Finset.mem_erase.mp hmp).1.symm,h.2.1,h.2.2⟩

/-- EXACT finite original all-odd-e source→(z,m',m) Parity
cofactor reindex on the *ACTUAL* Cauchy enlarged e≤2E and
n≤3V source, fixed signed nonzero k. The source complex function
W may retain all original α, H0, W1, signed ε, χ and η_eη_n.
The true physical source image counts each original e,m',n
exactly ONCE, even with P-primes dividing e. No guessed number
of source copies and no subset-norm inequality. -/
theorem parity_original_ungated_actual_fixed_m_k_sigma_signed_reindex434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k,
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q)) =
    ∑i∈(parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m),W i := by
  classical
  let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  have hS : ∀q∈S, Odd q.1 ∧ m≠q.2.1 ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
      parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k := by
    intro q hq
    have hh := parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Y m K k q hq
    exact ⟨hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2⟩
  exact parity_original_ungated_true_source_to_sigma_signed_reindex434
    d L band slot δ Y m k hk S hS W
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedActualSigmaImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- COMPLETE CORRECTED original B509 full-odd-e physical finite
source image embeds in the LITERAL positive unrestricted Parity
(4.17) Sigma(z,m',m) carrier. No e-Pfree assumption. The original
rough support is stated for m and m'∈K, which holds when the true
b629 fine α has nonzero coefficients; no false assumption that the
whole K interval must be rough is silently introduced in later
signed source estimates (unsupported indices have α=0).

The finite z set N must contain the actual source canonical z
values; this is exactly the natural source-to-Parity z interval
applicability obligation, not a postulated upper bound on a signed
sum. -/
theorem parity_original_ungated_actual_source_sigma_image_subset434
    (d : ℕ) (L E V : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K N : Finset ℕ) (k : ℤ)
    (hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hRoughK : ∀mp∈K,sourceD20Rough (Real.exp (Real.sqrt L)) mp)
    (hN : ∀q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k,
      parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2∈N) :
    (parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m) ⊆
    parityOriginalHistoricalActualB633PositiveSigma434 L k N := by
  intro i hi
  obtain ⟨q,hq,hqi⟩ := Finset.mem_image.mp hi
  have hLegal := parity_original_ungated_actual_fixed_m_k_source_legal434
    d L E V band slot δ Y m K k q hq
  rcases hLegal with ⟨he,hmp,hne,hOdd,hNe,hValid,hK⟩
  have hMpK : q.2.1∈K := (Finset.mem_erase.mp hmp).2
  have hForward := parity_original_ungated_true_source_in_positive_B633_sigma434
    d L hL band slot δ Y q.1 m q.2.1 q.2.2
    hOdd hNe hValid hRoughM (hRoughK q.2.1 hMpK)
    N (hN q hq)
  dsimp only at hForward
  rw [hK] at hForward
  have hIn : parityOriginalHistoricalUngatedSourceToSigma434 m q ∈
      parityOriginalHistoricalActualB633PositiveSigma434 L k N := hForward.2.2
  rw [←hqi]
  exact hIn

/-- EXACT original source-to-UNRESTRICTED-Sigma physical IMAGE
reindex for any complex signed weight: sum over the *actual*
all-odd-e e≤2E, real n≤3V, true B509 physical endpoints and
fixed signed k is exactly the sum over complete positive Sigma
FILTERED BY ITS GENUINE SOURCE IMAGE. This is a source-derived
indicator, not a fake restriction added to prove correlation
smallness; no signed subset is bounded by an unrestricted sum.
No multiplicity factor from e or n is present. -/
theorem parity_original_ungated_actual_source_as_positive_sigma_filter434
    (d : ℕ) (L E V : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K N : Finset ℕ) (k : ℤ) (hk : k≠0)
    (hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hRoughK : ∀mp∈K,sourceD20Rough (Real.exp (Real.sqrt L)) mp)
    (hN : ∀q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k,
      parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2∈N)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k,
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q)) =
    ∑i∈(parityOriginalHistoricalActualB633PositiveSigma434 L k N).filter
      (fun i => i ∈
        (parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
          d L E V band slot δ Y m K k).image
            (parityOriginalHistoricalUngatedSourceToSigma434 m)), W i := by
  classical
  let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let f := parityOriginalHistoricalUngatedSourceToSigma434 m
  let B := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  have hSub := parity_original_ungated_actual_source_sigma_image_subset434
    d L E V hL band slot δ Y m K N k hRoughM hRoughK hN
  have hImage : B.filter (fun i => i∈S.image f) = S.image f := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hi
      exact ⟨hSub hi,hi⟩
  rw [hImage]
  exact parity_original_ungated_actual_fixed_m_k_sigma_signed_reindex434
    d L E V band slot δ Y m K k hk W
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPsiZRange -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1900000

/-- The genuine fixed smooth positive dyadic source ψ(t),
supported STRICTLY in (1,4), forces every contributing literal
positive original z to belong to the exact unrestricted original
Parity(4.17) z-set `Finset.Icc 1 (floor(64 Z))` for Z>0.
This is NOT a sharp SOURCE cutoff replacing η_e,η_n:
it follows from the already proved C∞ ψ support, and it is the
precise automatic N-membership needed for the true full
odd-e source-to-Sigma injection at a fixed smooth Z. -/
theorem parity_original_actual_smooth_psi_supported_z_in_full_417_interval434
    (Z : ℝ) (hZ : 0 < Z) (z : ℕ)
    (hpsi : parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/Z)≠0) :
    z ∈ Finset.Icc 1 ⌊64*Z⌋₊ := by
  have hSupp := parity_original_historical_dyadic_psi_compact_positive_support434
    ((z:ℝ)/Z) hpsi
  have hzR : 0<(z:ℝ) := by
    have hh : (0:ℝ)<(z:ℝ)/Z := lt_trans (by norm_num) hSupp.1
    exact (div_pos_iff_of_pos_right hZ).mp hh
  have hz : 0<z := by exact_mod_cast hzR
  have hBound : (z:ℝ) < 4*Z := (div_lt_iff₀ hZ).mp hSupp.2
  have hz64 : (z:ℝ) ≤ 64*Z := by nlinarith [hZ]
  exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hz64⟩

/-- Original smooth ψ_Z makes ALL source events outside the
original unrestricted Parity z≤floor64Z interval EXACTLY ZERO,
without deleting any nonzero signed coefficient. The source
remaining e,n physical masks and χ phases are unchanged. -/
theorem parity_original_actual_psi_source_sum_restrict_full_417_interval434
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (z : ι → ℕ) (W : ι → ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∑q∈S,
      parityOriginalHistoricalDyadicSmoothPsi434 ((z q:ℝ)/Z)*W q) =
    ∑q∈S.filter (fun q => z q∈Finset.Icc 1 ⌊64*Z⌋₊),
      parityOriginalHistoricalDyadicSmoothPsi434 ((z q:ℝ)/Z)*W q := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : z q∈Finset.Icc 1 ⌊64*Z⌋₊
  · simp [hz]
  · have hpsi : parityOriginalHistoricalDyadicSmoothPsi434 ((z q:ℝ)/Z)=0 := by
      by_contra hne
      exact hz (parity_original_actual_smooth_psi_supported_z_in_full_417_interval434
        Z hZ (z q) hne)
    simp [hz,hpsi]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPsiSupportedSigma -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3700000

/-- EXACT source-supported original B509 full odd-e <=2E, n<=3V
fixed-m,k events after deleting ONLY zero factors of the original
fine alpha_m alpha_m' and true C∞ ψ(z/Z). No Pfree-e or
n/u smooth eta source gate is changed; the source image is a
TRUE subset with an EXACT complex signed equality (proved below),
not an estimated signed subcorrelation. -/
def parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    (d : ℕ) (L E V Z : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k).filter (fun q =>
      alpha m≠0 ∧ alpha q.2.1≠0 ∧
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z)≠0)

/-- Source-TRUE *unconditional upon the checked actual fine support*
full-odd-e physical ψ source IMAGE is contained in original
UNRESTRICTED Parity4.17 Sigma(z,m',m) over its exact `1..floor64Z`
z-domain. Only indices with nonzero real alpha/psi remain;
the needed P-prime-free facts concern rough m,m', NOT e, and
follow from the genuine original alpha rough bound. This holds
at fixed nonzero signed k for both signs of the original shift,
with ALL multiplicities of P-group primes in e and z retained. -/
theorem parity_original_ungated_actual_psi_nonzero_source_sub_full_417_sigma434
    (d : ℕ) (L E V Z : ℝ) (hL : 1≤L) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (hRough : ∀t,alpha t≠0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) t) :
    (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m) ⊆
      parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊) := by
  intro i hi
  obtain ⟨q,hq,hqi⟩ := Finset.mem_image.mp hi
  have hfilter := Finset.mem_filter.mp hq
  obtain ⟨hAm,hAmp,hPsi⟩ := hfilter.2
  have hLegal := parity_original_ungated_actual_fixed_m_k_source_legal434
    d L E V band slot δ Y m K k q hfilter.1
  obtain ⟨he,hmp,hn,hOdd,hNe,hValid,hK⟩ := hLegal
  have hZ : parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2∈
      Finset.Icc 1 ⌊64*Z⌋₊ :=
    parity_original_actual_smooth_psi_supported_z_in_full_417_interval434
      Z hZ (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2) hPsi
  have hForward := parity_original_ungated_true_source_in_positive_B633_sigma434
    d L hL band slot δ Y q.1 m q.2.1 q.2.2 hOdd hNe hValid
    (hRough m hAm) (hRough q.2.1 hAmp)
    (Finset.Icc 1 ⌊64*Z⌋₊) hZ
  dsimp only at hForward
  rw [hK] at hForward
  have hMember : parityOriginalHistoricalUngatedSourceToSigma434 m q ∈
      parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊) := hForward.2.2
  rw [←hqi]
  exact hMember

/-- The original signed full-odd-e physical source sum, with
literal fine alpha at m,m' and the actual C∞ ψ_Z, equals the
same source sum over nonzero factors. No original event is lost
when nonzero, because all discarded indices have IDENTICALLY
ZERO original complex amplitude. Does not use cancellation or
an external roughness/cardinality hypothesis. -/
theorem parity_original_ungated_actual_psi_alpha_exact_nonzero_restrict434
    (d : ℕ) (L E V Z : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let g : ℕ × (ℕ × ℕ) → ℂ := fun q =>
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z)
    (∑q∈S, g q*alpha m*star (alpha q.2.1)*
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q)) =
    ∑q∈parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha,
      g q*alpha m*star (alpha q.2.1)*
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q) := by
  classical
  dsimp only
  let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let g : ℕ × (ℕ × ℕ) → ℂ := fun q =>
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z)
  change (∑q∈S,g q*alpha m*star (alpha q.2.1)*
    W (parityOriginalHistoricalUngatedSourceToSigma434 m q)) =
    ∑q∈S.filter (fun q => alpha m≠0 ∧ alpha q.2.1≠0 ∧ g q≠0),
      g q*alpha m*star (alpha q.2.1)*
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ha : alpha m=0
  · simp [ha]
  by_cases hb : alpha q.2.1=0
  · simp [ha,hb]
  by_cases hg : g q=0
  · simp [ha,hb,hg]
  · simp [ha,hb,hg]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPsiSigmaSignedEquality -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- REAL full-odd-e original source → exact original UNRESTRICTED
Parity(4.17) positive Sigma image at fixed signed k and smooth dyadic
Z: for EVERY complex rest amplitude W_i, the full literal B509
source e≤2E, n≤3V, physical h=-2 endpoints and original alpha_m,
alpha_m' weights is EXACTLY equal to the full positive z∈[1,floor64Z]
Sigma correlation FILTERED by its TRUE physical source image.

No P-free e gate, no extra source z cap or hypothetical source-to-full
signed cancellation bound. The exact α-zero and ψ-zero terms are
shown zero BEFORE reindex, source map is INJECTIVE at fixed k,
and all remaining pairs satisfy genuine P-ordinary two-core divisors.
Only the original fine α rough support is required for nonzero
coefficients; it is proved for real b629 α in an existing native
source theorem. This proves the source-image equality, NOT equality
with all unrestricted Sigma terms. -/
theorem parity_original_ungated_actual_full_odd_psi_source_eq_real_417_sigma_image434
    (d : ℕ) (L E V Z : ℝ) (hL : 1≤L) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ)
    (hRough : ∀t,alpha t≠0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) t)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let f := parityOriginalHistoricalUngatedSourceToSigma434 m
    let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
      (Finset.Icc 1 ⌊64*Z⌋₊)
    let Sψ := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha
    (∑q∈S, parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
        alpha m * star (alpha q.2.1) * W (f q)) =
    ∑i∈B.filter (fun i => i∈Sψ.image f),
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        alpha m * star (alpha i.2.1) * W i := by
  classical
  dsimp only
  let S := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let f := parityOriginalHistoricalUngatedSourceToSigma434 m
  let Sψ := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y m K k alpha
  let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let Wfull : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      alpha m * star (alpha i.2.1) * W i
  have hZero := parity_original_ungated_actual_psi_alpha_exact_nonzero_restrict434
    d L E V Z band slot δ Y m K k alpha W
  change (∑q∈S,Wfull (f q)) = ∑q∈Sψ,Wfull (f q) at hZero
  have hLegal : ∀q∈Sψ,
      Odd q.1 ∧ m≠q.2.1 ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y q.1 m q.2.1 q.2.2 ∧
      parityOriginalHistoricalOffdiagK434 q.1 m q.2.1=k := by
    intro q hq
    have hb := (Finset.mem_filter.mp hq).1
    have hl := parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Y m K k q hb
    exact ⟨hl.2.2.2.1,hl.2.2.2.2.1,hl.2.2.2.2.2.1,hl.2.2.2.2.2.2⟩
  have hReindex := parity_original_ungated_true_source_to_sigma_signed_reindex434
    d L band slot δ Y m k hk Sψ hLegal Wfull
  have hSub : Sψ.image f ⊆ B :=
    parity_original_ungated_actual_psi_nonzero_source_sub_full_417_sigma434
      d L E V Z hL hZ band slot δ Y m K k alpha hRough
  have hImage : B.filter (fun i => i∈Sψ.image f)=Sψ.image f := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hi
      exact ⟨hSub hi,hi⟩
  change (∑q∈Sψ,Wfull (f q)) = ∑i∈Sψ.image f,Wfull i at hReindex
  change (∑q∈S,Wfull (f q)) = ∑i∈B.filter (fun i => i∈Sψ.image f),Wfull i
  rw [hImage]
  exact hZero.trans hReindex
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedActualFinePsiSigma -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2100000

/-- UNCONDITIONAL ORIGINAL r0=20 B629 fine α source-to-Sigma
physical image equality, not an assumed rough/prime support theorem.
The literal prime or rough full-cell α is chosen before L, the
nonzero source α_m,α_m' are PROVED exp(sqrt L)-rough via native
`parity_actual_fine_K_restricted_rough434`, and the correct full
odd-e≤2E,n≤3V h=-2 B509 populated physical source is mapped
injectively into Parity(4.17) z≤floor64Z positive ordinary-cofactor
Sigma. The exact C∞ ψ_Z and both actual α factors are inside
both complex sums. True e containing arbitrary P-prime powers
is retained. Signed cancellation of the unrestricted COMPLEMENT
is a distinct proven Fourier ghost-bound and its full integration
is not claimed here. -/
theorem parity_eventually_original_actual_fine_full_odd_psi_source_eq_417_sigma_image434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ), 2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (E V Z : ℝ), 0<Z →
      ∀ (Y m : ℕ) (K : Finset ℕ) (k : ℤ), k≠0 →
      ∀ (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let Sphysical := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot δ Y m K k
      let f := parityOriginalHistoricalUngatedSourceToSigma434 m
      let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
        d L E V Z band slot δ Y m K k alpha
      let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊)
      (∑q∈Sphysical,
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
          alpha m * star (alpha q.2.1) * W (f q)) =
      ∑i∈Ball.filter (fun i => i∈Spsi.image f),
        parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
          alpha m * star (alpha i.2.1) * W i := by
  filter_upwards [parity_actual_fine_K_restricted_rough434
    S beta gamma hS hbeta hgamma,
    eventually_ge_atTop (1:ℝ)] with L hRough hL
  refine ⟨hL,?_⟩
  intro prime l u hl hlow d band slot δ E V Z hZ Y m K k hk W
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  have hActualRough (t : ℕ) (ht : alpha t≠0) :
      sourceD20Rough (Real.exp (Real.sqrt L)) t :=
    hRough prime l u hl hlow K t ht
  exact parity_original_ungated_actual_full_odd_psi_source_eq_real_417_sigma_image434
    d L E V Z hL hZ band slot δ Y m K k hk alpha hActualRough W
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPsiPhysicalMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- The TRUE full-odd-e, full-n original physical SOURCE image
satisfies the EXACT B509 recovered physical predicate already
used by the source's full positive Sigma Fourier-ball/ghost
transfer. This is literal positive z, original k, real Q/P/H0
endpoint carrier, full n envelope and its genuine native binary
Z scale. No artificial support or e-Pfree assumption.
It proves image→physical, NOT the unproved converse that every
unrestricted physical-index predicate is in the e≤2E source
image (that converse needs the η_e/e-window support argument). -/
theorem parity_original_ungated_actual_psi_source_image_implies_B633_physical434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hi : i∈(parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m)) :
    ∃ en : ℕ, Odd en ∧ 0<en ∧
      ∃ n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y en i.2.2 K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
        parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1 := by
  obtain ⟨q,hq,hqi⟩ := Finset.mem_image.mp hi
  have hBase := (Finset.mem_filter.mp hq).1
  have hSource := parity_original_ungated_actual_fixed_m_k_source_legal434
    d L E V band slot δ Y m K k q hBase
  rcases q with ⟨e,⟨mp,n⟩⟩
  obtain ⟨hE,hMp,hN,hOdd,hNe,hValid,hK⟩ := hSource
  have hPhysical := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m mp n hOdd hNe hValid
  dsimp only at hPhysical
  have hZPos : 0<parityOriginalHistoricalCanonicalZ434 e m mp n := hPhysical.2.1
  have hKPrime : mp∈parityOriginalHistoricalKPrimeFibre434 e m K k := by
    unfold parityOriginalHistoricalKPrimeFibre434
    exact Finset.mem_filter.mpr ⟨hMp,hK⟩
  have hEvent : (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V)
      k (parityOriginalHistoricalActualZDyadicScale434
        (parityOriginalHistoricalCanonicalZ434 e m mp n)) := by
    unfold parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hKPrime,hN⟩,⟨hValid,hZPos,rfl⟩⟩
  rw [←hqi]
  exact ⟨e,hOdd,hOdd.pos,n,hN,hEvent,rfl⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPhysicalSmoothConverse -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3400000

/-- CONVERSE, conditional only on the **LITERAL NONZERO ORIGINAL
Schwartz SOURCE** (not on an invented e/n gate): every physically
populated B509 h=-2 pair (e,n,m,m',z) of the original full positive
Parity4.17 Sigma carrier lies in the *ACTUAL* full odd-e<=2E and
n<=3V e×m'×n Cauchy source image whenever the genuine physical
3D eta_e eta_n source kernel is nonzero at its exact logarithmic
triple and both original fine-alpha and fixed smooth psi_Z are
nonzero. The correct source e may contain P-group prime factors.

No complex signed-subsum inference and no artificial finite e/n
cutoff: e<2E follows from exact LOG PULLBACK of source eta_e;
n is already in the genuine full source eta_n envelope. -/
theorem parity_original_ungated_417_physical_schwartz_nonzero_in_true_source_image434
    (d : ℕ) (L E V U Z : ℝ) (hL : 8<=L)
    (hE : 0 < E) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length -> Bool)
    (Y m mp z : ℕ) (k : ℤ) (hk : k≠0) (K : Finset ℕ)
    (alpha : ℕ -> ℂ) (e n : ℕ)
    (he : Odd e) (hz : 0 < z)
    (hN : n ∈ parityOriginalHistoricalFullNEnvelope434 V)
    (hEvent : (mp,n) ∈
      parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 z))
    (hCanon : parityOriginalHistoricalCanonicalZ434 e m mp n=z)
    (hAlphaM : alpha m  ≠  0) (hAlphaMp : alpha mp  ≠  0)
    (hPsi : parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/Z)  ≠  0)
    (buf : ℝ -> ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ, buf x ≠ 0 -> a<=x ∧ x<=b)
    (hF : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)  ≠ 0) :
    ((⟨z,⟨mp,m⟩⟩ : Σ z : ℕ, Σ mp : ℕ, ℕ) ∈
      (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
        d L E V Z band slot δ Y m K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m)) := by
  classical
  have hEv := Finset.mem_filter.mp hEvent
  obtain ⟨hMpFiber, hNProduct⟩ := Finset.mem_product.mp hEv.1
  obtain ⟨hMpErase, hK⟩ := Finset.mem_filter.mp hMpFiber
  have hNe : m≠mp := (Finset.mem_erase.mp hMpErase).1.symm
  have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n := hEv.2.1
  have hm : 0 < m := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := by
    obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
    exact (Finset.mem_filter.mp hup).2.1
  have hDet := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hNe hValid
  rw [hK] at hDet
  obtain ⟨v,vp,vs,vps,hv,hvp,hMN,hMpN,_,_,_,_⟩ :=
    parity_original_historical_ungated_physical_valid_n_real_endpoints434
      d L band slot δ Y e m mp n he.pos hValid
  have hVeq : parityOriginalHistoricalCanonicalV434 e m n=v := by
    unfold parityOriginalHistoricalCanonicalV434
    have hh : m*n-2=e*v := by omega
    rw [hh, Nat.mul_div_cancel_left v he.pos]
  have hZprod : z=mp*v := by
    unfold parityOriginalHistoricalCanonicalZ434 at hCanon
    rw [hVeq] at hCanon
    exact hCanon.symm
  have hEta := parity_original_historical_reverse_real_log_nonzero_implies_actual_eta434
    L hL U E V Z e m mp n v z k hU hE hV hZ hm hmp hz hk
    hDet hMN hZprod buf a b hSmooth hBufSupport hF
  have hEbound := (parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
    L E V hL hE hV e n hEta).2.1
  have hEfloor : e≤⌊2*E⌋₊ := Nat.le_floor hEbound.le
  have hEFull : e∈parityOriginalHistoricalFullOddEEnvelope434 E := by
    unfold parityOriginalHistoricalFullOddEEnvelope434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hEfloor),he⟩
  have hSource : (e,(mp,n))∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k := by
    unfold parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨hEFull,Finset.mem_product.mpr ⟨hMpErase,hN⟩⟩
    · exact ⟨hValid,hK⟩
  have hSourcePsi : (e,(mp,n))∈parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha := by
    unfold parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    exact Finset.mem_filter.mpr ⟨hSource,⟨hAlphaM,hAlphaMp,by rw [hCanon];exact hPsi⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨(e,(mp,n)),hSourcePsi,?_⟩
  simp only [parityOriginalHistoricalUngatedSourceToSigma434,hCanon]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedPhysicalImageSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Exact original B509 full-odd-e physical SOURCE image predicate on
one unrestricted Parity(4.17) Sigma cofactor index, with the source
cofactor m=i.2.2 extracted from the native dependent Sigma. No
manually chosen e,n or a separate e-Pfree data type. -/
def parityOriginalHistoricalFullOddPsiImageAtSigma434
    (d : ℕ) (L E V Z : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ) : Prop :=
  i ∈ (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y i.2.2 K k alpha).image
      (parityOriginalHistoricalUngatedSourceToSigma434 i.2.2)

/-- On ANY physically populated original Parity (4.17) index, if the
source-construction's genuine nonlinear 3D Schwartz η_eη_n and
actual b629 α_m,α_m' and smooth ψ_Z are nonzero, its physical
B509 e/n witness MUST lie in the original FULL-ODD e<=2E,n<=3V
source image. No source Y/n/e sharp restriction is inserted: e<=2E
is a consequence of real η_e support via actual log-pullback. -/
theorem parity_original_ungated_physical_nonzero_implies_full_odd_psi_image434
    (d : ℕ) (L E V U Z : ℝ)
    (hL : 8≤L) (hE : 0 < E) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ) (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hz : 0 < i.1)
    (hPhys : ∃ en : ℕ, Odd en ∧ 0 < en ∧
      ∃ n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y en i.2.2 K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
        parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1)
    (hAlphaM : alpha i.2.2≠0) (hAlphaMp : alpha i.2.1≠0)
    (hPsi : parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)≠0)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hF : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)≠0) :
    parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i := by
  rcases i with ⟨z,⟨mp,m⟩⟩
  obtain ⟨en,hOdd,hEnPos,n,hN,hEvent,hCanon⟩ := hPhys
  exact parity_original_ungated_417_physical_schwartz_nonzero_in_true_source_image434
    d L E V U Z hL hE hV hU hZ band slot δ Y m mp z k hk K alpha
    en n hOdd hz hN hEvent hCanon hAlphaM hAlphaMp hPsi
    buf a b hSmooth hBufSupport hF
end Green64Analytic.Parity

end

end

