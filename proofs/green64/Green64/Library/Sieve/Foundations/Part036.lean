module

public import Green64.Library.Sieve.Foundations.Part035
public import Green64.Library.Sieve.Foundations.Part033
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part034
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part027
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Sieve / Foundations / Part036

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalLowfreqUngatedPhysicalOutsideImageZero -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- ACTUAL original Parity4.17 projected physical B509 terms outside the
FULL-ODD e<=2E,n<=3V correct SOURCE image have **zero full Fourier
signal**, pointwise after multiplication by the *original* nonlinear
η_eη_n Schwartz kernel. This is not zero at each χ separately and
not necessarily zero after restricting the Fourier integral to a
ball; the ball discrepancy must be paid by the source H-moment.

Here A is ANY character-free B633 physical atom (in application the
literal H0/W1/epsilon/phase B633 coefficient); the two actual fine
alpha factors, genuine smooth ψ_Z and original integer-odd projector
remain explicit. There is NO source e-Pfree or artificial sharp gate. -/
theorem parity_original_ungated_physical_outside_full_odd_image_weighted_zero434
    (d : ℕ) (L E V U Z : ℝ)
    (hL : 8≤L) (hE : 0 < E) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ) (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hz : 0 < i.1)
    (hPhysical : ∃ en : ℕ, Odd en ∧ 0 < en ∧
      ∃ n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y en i.2.2 K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
        parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1)
    (hOutside : ¬parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i)
    (A : ℂ) (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b) :
    (parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        A * alpha i.2.2 * star (alpha i.2.1) *
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
         then (1:ℂ) else 0)) *
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hSmooth hBufSupport
        (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1) = 0 := by
  let g := parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)
  let w : ℂ := (g*A*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0))
  change w*f=0
  by_contra hnz
  have hg : g≠0 := by
    intro hzero
    apply hnz
    simp only [w,hzero,zero_mul]
  have ha : alpha i.2.2≠0 := by
    intro hzero
    apply hnz
    simp only [w,hzero,mul_zero,zero_mul]
  have hb : alpha i.2.1≠0 := by
    intro hzero
    apply hnz
    simp only [w,hzero,star_zero,mul_zero,zero_mul]
  have hf : f≠0 := by
    intro hzero
    apply hnz
    simp only [hzero,mul_zero]
  have himage := parity_original_ungated_physical_nonzero_implies_full_odd_psi_image434
    d L E V U Z hL hE hV hU hZ band slot δ Y K k hk alpha i hz
    hPhysical ha hb hg buf a b hSmooth hBufSupport hf
  exact hOutside himage
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedSourceImageBallTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3300000

/-- The actual B509 source-image Fourier BALL, not only its full
Fourier integral, is controlled by the genuine physical source
ball PLUS the explicitly paid Schwartz moment of the extra physical
indices. The complete source image is the real full-odd-e<=2E,
n<=3V Q/P/H0 support with actual alpha and psi, no Pfree e.
The proof never bounds a selected complex sum by the unrestricted
signed sum; all missing physical terms have zero weighted full
Schwartz signal, so only their truncated Fourier tails are charged. -/
theorem parity_original_actual_full_odd_source_image_ball_le_physical_plus_ghost434
    (d : ℕ) (L E V U Z : ℝ)
    (hL : 8≤L) (hE : 0 < E) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ)
    (s : Finset (Σ z : ℕ, Σ mp : ℕ, ℕ))
    (hS : ∀i∈s,0 < i.1)
    (A : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (H : ℕ) (T : ℝ) (hT : 0 < T) :
    let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
    let physical : I → Prop := fun i =>
      ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ Y en i.2.2 K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
        parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1
    let image : I → Prop := fun i =>
      parityOriginalHistoricalFullOddPsiImageAtSigma434
        d L E V Z band slot δ Y K k alpha i
    let W : I → ℂ := fun i =>
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
        A i * alpha i.2.2 * star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
          then (1:ℂ) else 0)
    let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
      parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
    ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter image) W t f ζ‖ ≤
    ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (s.filter physical) W t f ζ‖ +
    parityOriginal3DPhysicalFiniteCoefficientMass434
      ((s.filter physical).filter (fun i => ¬image i)) W *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  classical
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let physical : I → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y en i.2.2 K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
      parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1
  let image : I → Prop := fun i =>
    parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i
  let W : I → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
      A i*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0)
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  have hImagePhysical : ∀ i∈s, image i → physical i := by
    intro i hi him
    exact parity_original_ungated_actual_psi_source_image_implies_B633_physical434
      d L E V Z band slot δ Y i.2.2 K k alpha i him
  have hFilterEq : (s.filter physical).filter image=s.filter image := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
         (Finset.mem_filter.mp hi).2⟩
    · intro hi
      obtain ⟨hs,him⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hs,hImagePhysical i hs him⟩,him⟩
  have hZero : ∀i∈s.filter physical, ¬image i → W i *
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hSmooth hBufSupport (t i)=0 := by
    intro i hi hNot
    obtain ⟨hs,hPhys⟩ := Finset.mem_filter.mp hi
    exact parity_original_ungated_physical_outside_full_odd_image_weighted_zero434
      d L E V U Z hL hE hV hU hZ band slot δ Y K k hk
      alpha i (hS i hs) hPhys hNot (A i) buf a b hSmooth hBufSupport
  have hTransfer := parity_original_historical_weighted_3d_source_ball_le_full_plus_ghost434
    (s.filter physical) image W t H L hL U E V Z k
    buf a b hSmooth hBufSupport T hT hZero
  rw [hFilterEq] at hTransfer
  exact hTransfer
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullOddSourceBallEq417 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- REAL corrected full-odd e<=2E, n<=3V source-image projected
B633 lowfrequency 3D Fourier ball at fixed original (k,Z) is
controlled by the COMPLETE signed unrestricted Parity4.17 χ-summed
Fourier ball plus exactly TWICE the source-proven positive original
B633 Sigma ghost mass times true finite Schwartz H-moment/T^H.
The two charges are (a) source-image complement inside true B509
physical predicate, (b) physical complement inside unrestricted
Sigma. Both full Fourier ghost signals are zero for real source
reasons, and their BALL errors are paid without assuming signed
subsum monotonicity. The source-image has literal genuine b629 fine
alpha, original h=-2, full odd e with possible P-prime factors,
true C∞ psi_Z and H0/W1/epsilon cofactor atoms. This does NOT
identify the literal full Bprime physical-source coefficient outer
with the Sigma image Fourier source, or sum k,Z/fine families. -/
theorem parity_eventually_original_actual_B633_full_odd_source_image_psi_ball_le_eq417_plus_two_ghost434
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
      let image : I → Prop := fun i =>
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ (Nat.ceil (6*U*V)) K k alpha i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (s.filter image) Wproj t f ζ‖ ≤
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
      2 * ((L^(2*parityOriginalW1PolylogExponent434)*
          ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  filter_upwards [parity_eventually_original_actual_B633_psi_ball_le_eq417_plus_proven_polylog_ghost434
      S beta gamma Ck hS hbeta hgamma,
    parity_eventually_original_B633_any_sigma_ghost_positive_mass_polylog434
      S beta gamma Ck hS hbeta hgamma] with L hPhysicalL hGhostL
  refine ⟨hPhysicalL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN hkZ buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let s : Finset I := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let Wproj : I → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
      A i*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0)
  let physical : I → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0 < en ∧ ∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (i.2.1,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) en i.2.2 K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 i.1) ∧
      parityOriginalHistoricalCanonicalZ434 en i.2.2 i.2.1 n=i.1
  let image : I → Prop := fun i =>
    parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ (Nat.ceil (6*U*V)) K k alpha i
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  let M : ℝ := L^(2*parityOriginalW1PolylogExponent434)*
    ((Nat.ceil (65*Z):ℕ):ℝ)*(1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15
  let B : ℝ := parityOriginal3DSourceMomentFiniteBudget434 H f/T^H
  let G : ℂ := ∑chi : DirichletCharacter ℂ (2*k.natAbs),
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
         parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha F.residual
          (2*k.natAbs) chi F.lo F.hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ))
  let ball (Q : I → Prop) : ℂ :=
    ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 (s.filter Q) Wproj t f ζ
  have hPos : ∀i∈s,0 < i.1 := by
    intro i hi
    have hPair := parity_original_historical_actual_positive_sigma_is_legal_cofactor434
      L k N hN i hi
    exact hPair.2.2.1
  have hPhys := hPhysicalL.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    N hN hkZ buf a b hSmooth hBufSupport H T hT
  change ‖ball physical‖ ≤ ‖G‖ + M*B at hPhys
  have hImage := parity_original_actual_full_odd_source_image_ball_le_physical_plus_ghost434
    d L E V U Z hLw hE hV hU hZ band slot δ
    (Nat.ceil (6*U*V)) K k hk alpha s hPos A
    buf a b hSmooth hBufSupport H T hT
  change ‖ball image‖ ≤ ‖ball physical‖ +
    parityOriginal3DPhysicalFiniteCoefficientMass434
      ((s.filter physical).filter (fun i=>¬image i)) Wproj*B at hImage
  have hGhost := hGhostL.2 prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 Z signed N hZ hkZ image
  have hW (i : I) : Wproj i =
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
      (A i*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0)) := by
    dsimp [Wproj]
    ring
  have hMass : parityOriginal3DPhysicalFiniteCoefficientMass434
      ((s.filter physical).filter (fun i=>¬image i)) Wproj ≤ M := by
    have hSub : (s.filter physical).filter (fun i=>¬image i) ⊆
        s.filter (fun i=>¬image i) := by
      intro i hi
      obtain ⟨hp,hnot⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,hnot⟩
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun i hi hnot => norm_nonneg (Wproj i))
    have hGhost' : (∑i∈s.filter (fun i=>¬image i), ‖Wproj i‖) ≤ M := by
      have hEqual : (∑i∈s.filter (fun i=>¬image i), ‖Wproj i‖) =
          ∑i∈s.filter (fun i=>¬image i),
          ‖parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
          (A i*alpha i.2.2*star (alpha i.2.1)*
          (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
            then (1:ℂ) else 0))‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hW i]
      change (∑i∈s.filter (fun i=>¬image i),
          ‖parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)*
            (A i*alpha i.2.2*star (alpha i.2.1)*
            (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
              then (1:ℂ) else 0))‖) ≤ M at hGhost
      exact hEqual.trans_le hGhost
    exact hs.trans hGhost'
  have hB : 0≤B := by
    unfold B parityOriginal3DSourceMomentFiniteBudget434
      parityOriginal3DSourceFiniteSeminormBudget434
    have hC := parity_original_3d_source_geometric_constant_nonneg434
    positivity
  change ‖ball image‖ ≤ ‖G‖+2*(M*B)
  calc
    _ ≤ ‖ball physical‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        ((s.filter physical).filter (fun i=>¬image i)) Wproj*B := hImage
    _ ≤ ‖ball physical‖ + M*B := by
      simpa only [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right hMass hB) (‖ball physical‖))
    _ ≤ (‖G‖+M*B)+M*B := by
      simpa only [add_comm] using (add_le_add_right hPhys (M*B))
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUngatedSourceOddMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Literal corrected h=-2 original Cauchy physical pair with odd
source e and its ACTUAL canonical signed off-diagonal shift k:
Parity(2.6)'s WHOLE-CHARACTER odd-integral e detector is exactly 1.
No oddness/congruence premise is artificially imposed on unrestricted
B633 pairs. This is only asserted for genuine physical B509 e,m,m',n. -/
theorem parity_original_ungated_actual_source_odd_shift_mask_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (k : ℤ) (he : Odd e)
    (hNe : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hK : parityOriginalHistoricalOffdiagK434 e m mp=k) :
    (if k∣(mp:ℤ)-(m:ℤ) ∧ Odd (((mp:ℤ)-(m:ℤ))/k)
      then (1:ℂ) else 0) = 1 := by
  have hDet := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hNe hValid
  rw [hK] at hDet
  have hk : k≠0 := by
    intro hzero
    rw [hzero,mul_zero] at hDet
    have hh : mp=m := by exact_mod_cast (sub_eq_zero.mp hDet)
    exact hNe hh.symm
  have hdiv : k∣(mp:ℤ)-(m:ℤ) := ⟨(e:ℤ),by rw [hDet];ring⟩
  have hquot : ((mp:ℤ)-(m:ℤ))/k = (e:ℤ) := by
    rw [hDet]
    rw [mul_comm (e:ℤ) k]
    exact Int.mul_ediv_cancel_left (e:ℤ) hk
  have hodd : Odd (((mp:ℤ)-(m:ℤ))/k) := by
    rw [hquot]
    exact_mod_cast he
  simp [hdiv,hodd]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullOddSourceChiCoefficient -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- EXACT ORIGINAL r0=20 h=-2 full-odd e<=2E,n<=3V source
B633 signed COEFFICIENT sum, at fixed original (k,Z,m), with
original reserved-B509 Q prime H0 residual, W1, epsilon, b629
fine alpha and smooth ψ_Z, equals the ENTIRE Parity(2.6) character
sum of original B633 cofactor pairs over EXACTLY its true finite
positive Sigma source IMAGE. Genuine source odd e has odd shift
mask=1, proved from the physical determinant. Character projection
precedes the natural source-image filter, never an attempted χ-wise
signed-subset inequality. No Pfree-e requirement, no artificial
e/n cutoff, and no #e,#n,#χ source multiplicity. This is an
exact fixed-(k,Z) signed source/coefficient equality, not an
estimate for all unrestricted Parity(4.17) pairs. -/
theorem parity_eventually_original_actual_full_odd_source_chi_cofactor_exact434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 E V Z : ℝ) (signed : Bool),
      0 < Z → ∀ (Y m : ℕ),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let f := parityOriginalHistoricalUngatedSourceToSigma434 m
      let Sphysical := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot δ Y m K k
      let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
        d L E V Z band slot δ Y m K k alpha
      let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊)
      (∑q∈Sphysical, psi (f q)*alpha m*star (alpha q.2.1)*A (f q)) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∑i∈Ball.filter (fun i => i∈Spsi.image f),
            let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
              (2*k.natAbs) chi 0 0
            psi i * parityOriginalHistoricalB633PhysicalPairTerm434
              L rho xi1 xi2 xi3 signed alpha F.residual
              (2*k.natAbs) chi F.lo F.hi
              i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)) := by
  filter_upwards [parity_eventually_original_actual_fine_full_odd_psi_source_eq_417_sigma_image434
      S beta gamma hS hbeta hgamma,
    parity_eventually_original_actual_B633_pointwise_full_chi434
      S beta gamma Ck hS hbeta hgamma] with L hSigma hChi
  refine ⟨hSigma.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 E V Z signed hZ Y m
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let f := parityOriginalHistoricalUngatedSourceToSigma434 m
  let source := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y m K k alpha
  let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let selected := Ball.filter (fun i => i∈Spsi.image f)
  let mask : I → ℂ := fun i =>
    if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
      then 1 else 0
  let Pair : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ := fun chi i =>
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
      (2*k.natAbs) chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual
      (2*k.natAbs) chi F.lo F.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  have hMask (q : ℕ × (ℕ × ℕ)) (hq : q∈source) : mask (f q)=1 := by
    have hLegal := parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Y m K k q hq
    obtain ⟨he,hmp,hn,hOdd,hNe,hValid,hK⟩ := hLegal
    change (if k∣(q.2.1:ℤ)-(m:ℤ) ∧
        Odd (((q.2.1:ℤ)-(m:ℤ))/k) then (1:ℂ) else 0)=1
    exact parity_original_ungated_actual_source_odd_shift_mask_one434
      d L band slot δ Y q.1 m q.2.1 q.2.2 k hOdd hNe hValid hK
  have hWithMask : (∑q∈source,
      psi (f q)*alpha m*star (alpha q.2.1)*A (f q)) =
    ∑q∈source,psi (f q)*alpha m*star (alpha q.2.1)*
      (A (f q)*mask (f q)) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hMask q hq]
    ring
  have hSigmaEq := hSigma.2 prime l u hl hlow d band slot δ E V Z hZ
    Y m K k hk (fun i : I => A i*mask i)
  change (∑q∈source, psi (f q)*alpha m*star (alpha q.2.1)*
      (A (f q)*mask (f q))) =
    ∑i∈selected,psi i*alpha m*star (alpha i.2.1)*(A i*mask i) at hSigmaEq
  have hPoint (i : I) :
      (A i*alpha i.2.2*star (alpha i.2.1))*mask i =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * Pair chi i := by
    exact hChi.2 prime l u hl hlow K k hk hkBound d band slot δ ξ
      rho xi1 xi2 xi3 signed i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  have hSelectedM (i : I) (hi : i∈selected) : i.2.2=m := by
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
    have hh := congrArg (fun j : I => j.2.2) heq
    simpa [f,parityOriginalHistoricalUngatedSourceToSigma434] using hh.symm
  have hTerm (i : I) (hi : i∈selected) :
      psi i*alpha m*star (alpha i.2.1)*(A i*mask i) =
      ∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * (psi i*Pair chi i) := by
    have hh := hPoint i
    rw [hSelectedM i hi] at hh
    calc
      _ = psi i*((A i*alpha m*star (alpha i.2.1))*mask i) := by ring
      _ = psi i*(∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * Pair chi i) := by rw [hh]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi hchi
        ring
  calc
    (∑q∈source, psi (f q)*alpha m*star (alpha q.2.1)*A (f q)) =
      ∑q∈source,psi (f q)*alpha m*star (alpha q.2.1)*
        (A (f q)*mask (f q)) := hWithMask
    _ = ∑i∈selected,psi i*alpha m*star (alpha i.2.1)*(A i*mask i) := hSigmaEq
    _ = ∑i∈selected,∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi * (psi i*Pair chi i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hTerm i hi
    _ = ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      ∑i∈selected,parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (psi i*Pair chi i) := Finset.sum_comm
    _ = ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑i∈selected,psi i*Pair chi i) := by
      apply Finset.sum_congr rfl
      intro chi hchi
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633AtomThreeFourierShift -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- EXACT original B633 Q/B509 reserved-prime CHARACTER-FREE atom
carries the three Mellin/Fourier powers. Multiplication by the
ACTUAL normalized Parity (4.14) Euclidean 3D log phase shifts ALL
THREE source frequencies by 2πζ_j and produces exactly the common
U,U,Z scale factor of modulus one. The true B509 residual H0,
W1, both signed epsilon, rho phase and shifted z+2k are unchanged;
positive m,m',z are the only required arithmetic hypotheses. This
is the character-free piece absent from the previous full χ phase
bridge and does not use any source or signed cancellation estimate. -/
theorem parity_original_literal_B633_character_free_atom_three_fourier_shift434
    (L rho xi1 xi2 xi3 U Z : ℝ)
    (m mp z zp : ℕ) (signed : Bool)
    (residual : ℕ → ℂ) (lo hi : ℕ)
    (ζ : EuclideanSpace ℝ (Fin 3))
    (hU : 0 < U) (hZ : 0 < Z)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) :
    parityOriginalHistoricalB633CharacterFreeAtom434
      L rho xi1 xi2 xi3 signed residual lo hi m mp z zp *
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z) =
    parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
      parityOriginalHistoricalB633CharacterFreeAtom434
        L rho (xi1+2*Real.pi*(ζ 0))
          (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
          signed residual lo hi m mp z zp := by
  rw [parity_original_historical_three_log_phases_to_parity_416434
      U Z hU hZ m mp z hm hmp hz ζ]
  unfold parityOriginalHistoricalB633ThreeFourierScale434
    parityOriginalHistoricalB633CharacterFreeAtom434
  rw [parity_original_physical_imaginary_power_add434 m hm xi1 (2*Real.pi*(ζ 0)),
      parity_original_physical_imaginary_power_add434 mp hmp xi2 (2*Real.pi*(ζ 1)),
      parity_original_physical_imaginary_power_add434 z hz xi3 (2*Real.pi*(ζ 2))]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullOddSourceFourierChi -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3900000

/-- ACTUAL Parity(4.10)-(4.17) fixed-(m,k,Z,ζ) original B509
full-odd-e<=2E,n<=3V complex SOURCE Fourier integrand: the
complete original 3D normalized logarithmic twist of the literal
B633 α/H0/W1/ε character-free physical coefficient is exactly the
one original U,U,Z scale factor times the FULL original Parity(2.6)
χ-projected B633 two-cofactor sum on the genuine source-image
Sigma filter, with shifted frequencies ξ_j+2πζ_j.

This is a literal coefficient identity on the correct finite
natural e,n source, NOT just a generic weighted source wrapper.
The physical source e can have P-group factors; no cardinality
factor #e/#n/#χ and no monotonicity of signed subcorrelations.
It is the core algebraic Fourier-source equality needed to combine
the previous two-ghost source IMAGE ball with original (4.17)
pointwise saving. Fixed k,Z only, no outer k/Z summation here. -/
theorem parity_eventually_original_actual_full_odd_source_three_fourier_chi_exact434
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
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool)
        (ζ : EuclideanSpace ℝ (Fin 3)),
      0<U → 0<Z → ∀ (Y m : ℕ),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let f := parityOriginalHistoricalUngatedSourceToSigma434 m
      let Sphysical := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot δ Y m K k
      let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
        d L E V Z band slot δ Y m K k alpha
      let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊)
      (∑q∈Sphysical,
        (psi (f q)*alpha m*star (alpha q.2.1)*A (f q))*
          parityOriginal3DPhysicalLogFourierPhase434 ζ
            (parityOriginalHistoricalRealLogTriple434 U Z m q.2.1
              (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2))) =
      parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ *
        (∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            (∑i∈Ball.filter (fun i => i∈Spsi.image f),
              let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
                (2*k.natAbs) chi 0 0
              psi i * parityOriginalHistoricalB633PhysicalPairTerm434
                L rho (xi1+2*Real.pi*(ζ 0))
                  (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
                  signed alpha F.residual (2*k.natAbs) chi F.lo F.hi
                  i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat))) := by
  filter_upwards [parity_eventually_original_actual_full_odd_source_chi_cofactor_exact434
    S beta gamma Ck hS hbeta hgamma] with L hChi
  refine ⟨hChi.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed ζ hU hZ Y m
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let AShift : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho (xi1+2*Real.pi*(ζ 0))
      (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
      signed F0.residual F0.lo F0.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let f := parityOriginalHistoricalUngatedSourceToSigma434 m
  let source := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y m K k alpha
  let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let scale := parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ
  have hTerm (q : ℕ × (ℕ × ℕ)) (hq : q∈source) :
      (psi (f q)*alpha m*star (alpha q.2.1)*A (f q))*
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalRealLogTriple434 U Z m q.2.1
            (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2)) =
      scale*(psi (f q)*alpha m*star (alpha q.2.1)*AShift (f q)) := by
    have hLegal := parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Y m K k q hq
    obtain ⟨he,hmp,hn,hOdd,hNe,hValid,hK⟩ := hLegal
    have hm : 0 < m := by
      obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
      exact (Finset.mem_filter.mp hu).2.1
    have hmpPos : 0 < q.2.1 := by
      obtain ⟨u,hu,up,hup,_,_,_,_⟩ := hValid
      exact (Finset.mem_filter.mp hup).2.1
    have hz : 0 < parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2 :=
      (parity_original_historical_ungated_physical_valid_k_z434
        d L band slot δ Y q.1 m q.2.1 q.2.2 hOdd hNe hValid).2.1
    have hShift := parity_original_literal_B633_character_free_atom_three_fourier_shift434
      L rho xi1 xi2 xi3 U Z m q.2.1
      (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2)
      ((((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℤ)+2*k).toNat))
      signed F0.residual F0.lo F0.hi ζ hU hZ hm hmpPos hz
    change A (f q)*
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z m q.2.1
          (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2)) =
      scale*AShift (f q) at hShift
    calc
      _ = (psi (f q)*alpha m*star (alpha q.2.1)) *
        (A (f q)*parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalRealLogTriple434 U Z m q.2.1
            (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2))) := by ring
      _ = (psi (f q)*alpha m*star (alpha q.2.1))*(scale*AShift (f q)) := by
        rw [hShift]
      _ = _ := by ring
  have hSumShift :
      (∑q∈source,
        (psi (f q)*alpha m*star (alpha q.2.1)*A (f q))*
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalRealLogTriple434 U Z m q.2.1
            (parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2))) =
      scale*(∑q∈source,psi (f q)*alpha m*star (alpha q.2.1)*AShift (f q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact hTerm q hq
  have hCoef := hChi.2 prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) E V Z signed hZ Y m
  change (∑q∈source,psi (f q)*alpha m*star (alpha q.2.1)*AShift (f q)) =
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑i∈Ball.filter (fun i=>i∈Spsi.image f),
          let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
            (2*k.natAbs) chi 0 0
          psi i * parityOriginalHistoricalB633PhysicalPairTerm434
            L rho (xi1+2*Real.pi*(ζ 0))
              (xi2+2*Real.pi*(ζ 1)) (xi3+2*Real.pi*(ζ 2))
              signed alpha F.residual (2*k.natAbs) chi F.lo F.hi
              i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)) at hCoef
  exact hSumShift.trans (congrArg (fun w : ℂ => scale*w) hCoef)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullOddSourceTwistedExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4100000

/-- Exact actual original full-odd e<=2E,n<=3V B509 physical
SOURCE finite 3D Fourier integrand, with the TRUE Ybox=ceil(6UV),
b629 fine α, original H0 residual, W1 and signed epsilon:

  (Fourier f)(ζ) ∑_(e,m',n actual) ψ(z/Z) α_m α̅_m' A_B633(z,m',m)
                                      exp(2πi⟪ζ,log(m/U,m'/U,z/Z)⟫)

EQUALS the literal Fourier-transform-multiplied, fully projected
original B633 finite physical kernel on EXACTLY the actual source
Sigma image, using the same original Schwartz η_eη_n kernel.

No missing source coefficient, no fabricated per-character gate,
no hidden e/n/multiplicity factors and no per-subset signed norm
inequality. Crucially the equality is POINTWISE in Fourier ζ and
uses the true original normalized 2π logarithmic phase. It does
not claim the unrestricted signed Parity4.17 saving or global Type II. -/
theorem parity_eventually_original_actual_full_odd_B509_source_twisted_eq_sigma_image434
    (S beta gamma : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      ∀ (m : ℕ) (ζ : EuclideanSpace ℝ (Fin 3))
        (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
      let Ybox := Nat.ceil (6*U*V)
      let Sphysical := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot δ Ybox m K k
      let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
        d L E V Z band slot δ Ybox m K k alpha
      let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊)
      let image : I → Prop := fun i => i∈Spsi.image fmap
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      let Wproj : I → ℂ := fun i => psi i*A i*alpha i.2.2*star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
          then (1:ℂ) else 0)
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑q∈Sphysical,
          (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
            parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))) =
      parityOriginal3DPhysicalFiniteTwistedSource434
        (Ball.filter image) Wproj t f ζ := by
  filter_upwards [parity_eventually_original_actual_fine_full_odd_psi_source_eq_417_sigma_image434
      S beta gamma hS hbeta hgamma,
    eventually_ge_atTop (8:ℝ)] with L hSigma hLw
  refine ⟨hLw,?_⟩
  intro hLw' prime l u hl hlow K k hk d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ
    m ζ buf a b hSmooth hBufSupport
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
  let Ybox := Nat.ceil (6*U*V)
  let source := parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Ybox m K k
  let Spsi := parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Ybox m K k alpha
  let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let image : I → Prop := fun i => i∈Spsi.image fmap
  let selected := Ball.filter image
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw' U E V Z k buf a b hSmooth hBufSupport
  let mask : I → ℂ := fun i =>
    if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
      then 1 else 0
  let Wproj : I → ℂ := fun i =>
    psi i*A i*alpha i.2.2*star (alpha i.2.1)*mask i
  let W0 : I → ℂ := fun i => A i*mask i*
    parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)
  have hMask (q : ℕ × (ℕ × ℕ)) (hq : q∈source) : mask (fmap q)=1 := by
    have hLegal := parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Ybox m K k q hq
    obtain ⟨he,hmp,hn,hOdd,hNe,hValid,hK⟩ := hLegal
    change (if k∣(q.2.1:ℤ)-(m:ℤ) ∧
        Odd (((q.2.1:ℤ)-(m:ℤ))/k) then (1:ℂ) else 0)=1
    exact parity_original_ungated_actual_source_odd_shift_mask_one434
      d L band slot δ Ybox q.1 m q.2.1 q.2.2 k hOdd hNe hValid hK
  have hEq := hSigma.2 prime l u hl hlow d band slot δ E V Z hZ
    Ybox m K k hk W0
  change (∑q∈source,psi (fmap q)*alpha m*star (alpha q.2.1)*W0 (fmap q)) =
    ∑i∈selected,psi i*alpha m*star (alpha i.2.1)*W0 i at hEq
  have hSource :
      (∑q∈source,
        (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
          parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))) =
      ∑q∈source,psi (fmap q)*alpha m*star (alpha q.2.1)*W0 (fmap q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hh := hMask q hq
    dsimp only [W0]
    rw [hh]
    ring
  have hSelectedM (i : I) (hi : i∈selected) : i.2.2=m := by
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
    have hh := congrArg (fun j : I => j.2.2) heq
    simpa [fmap,parityOriginalHistoricalUngatedSourceToSigma434] using hh.symm
  have hDest :
      (∑i∈selected,psi i*alpha m*star (alpha i.2.1)*W0 i) =
      ∑i∈selected,Wproj i*parityOriginal3DPhysicalLogFourierPhase434 ζ (t i) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [W0,Wproj]
    rw [hSelectedM i hi]
    ring
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
  change (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑q∈source,
        (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
          parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))) =
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑i∈selected,Wproj i*parityOriginal3DPhysicalLogFourierPhase434 ζ (t i))
  rw [hSource,hEq,hDest]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqCofactorMImagePartition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- EXACT finite original cofactor-m partition algebra. If a
physical source image on original dependent Sigma(z,m',m) is
supported on the genuine fine K cofactor, summing signed complex
weights over all original m in K and each exact m-fibre counts
every genuine source image exactly once. In particular no #m
multiplier, complex triangle bound or P-free-e gate is required.
This is a finite identity, not a signed-subsum inequality. -/
theorem parity_original_actual_full_odd_cofactor_m_fibre_sum_exact434
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (K : Finset ℕ)
    (m : ι → ℕ) (physical : ι → Prop) (W : ι → ℂ)
    (hSupport : ∀i∈s, physical i → m i∈K) :
    (∑a∈K, ∑i∈s.filter (fun i => m i=a ∧ physical i), W i) =
      ∑i∈s.filter physical,W i := by
  classical
  calc
    _ = ∑a∈K,∑i∈s,
        if m i=a ∧ physical i then W i else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_filter]
    _ = ∑i∈s,∑a∈K,
        if m i=a ∧ physical i then W i else 0 := Finset.sum_comm
    _ = ∑i∈s, if physical i then W i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hp : physical i
      · have hm := hSupport i hi hp
        simp [hp, hm]
      · simp [hp]
    _ = _ := by rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFineMSourceImagePartition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2700000

/-- EXACT original source-image cofactor-m fibre predicate:
(e,m',n)->(z,m',m) at a fixed source m is in the image if and
only if the indexed unrestricted Sigma cofactor equals m and
that Sigma index belongs to the TRUE full odd-e source image
with its own native m. No m-independence, character positivity,
or extra e/n support is assumed. -/
theorem parity_original_actual_full_odd_psi_sigma_m_fibre_iff434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (m : ℕ) (i : Σ z : ℕ, Σ mp : ℕ, ℕ) :
    i∈(parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m) ↔
    i.2.2=m ∧ parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i := by
  constructor
  · intro hi
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hi
    have hM : i.2.2=m := by
      have hh := congrArg (fun j : Σ z : ℕ, Σ mp : ℕ, ℕ => j.2.2) heq
      simpa [parityOriginalHistoricalUngatedSourceToSigma434] using hh.symm
    refine ⟨hM,?_⟩
    change i∈(parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y i.2.2 K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 i.2.2)
    simpa only [hM] using hi
  · rintro ⟨hM,hi⟩
    change i∈(parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y i.2.2 K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 i.2.2) at hi
    simpa only [hM] using hi

/-- For the ACTUAL K-restricted b629 α_m, the genuine nonzero
full-odd source image has its extracted cofactor m in K.
This is a consequence of the **literal nonzero α_m** in the
source predicate, NOT an assumption that all source m or e are
rough, and carries no #m multiplicity penalty. -/
theorem parity_original_actual_full_odd_psi_sigma_image_m_in_fine_K434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (a : ℕ → ℂ)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hi : parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k (restrictSequence K a) i) :
    i.2.2∈K := by
  obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hi
  have ha : restrictSequence K a i.2.2 ≠ 0 :=
    (Finset.mem_filter.mp hq).2.1
  by_contra hnot
  exact ha (by simp [restrictSequence,hnot])

/-- COMPLETE actual b629 ORIGINAL K-cofactor source-image
reindex: the finite χ/Fourier-source images at all m∈K are
DISJOINT and partition the entire nonzero full-odd e,n source
Sigma image. In the precise algebraic statement, every original
complex signed weight W is preserved without taking absolute
values or paying #m (or #e/#n). -/
theorem parity_original_actual_full_odd_psi_sigma_complete_m_partition434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (a : ℕ → ℂ)
    (B : Finset (Σ z : ℕ, Σ mp : ℕ, ℕ))
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    let alpha := restrictSequence K a
    let physical : (Σ z : ℕ, Σ mp : ℕ, ℕ) → Prop := fun i =>
      parityOriginalHistoricalFullOddPsiImageAtSigma434
        d L E V Z band slot δ Y K k alpha i
    (∑m∈K,
      ∑i∈B.filter (fun i => i∈
        (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
          d L E V Z band slot δ Y m K k alpha).image
          (parityOriginalHistoricalUngatedSourceToSigma434 m)),W i) =
    ∑i∈B.filter physical,W i := by
  classical
  dsimp only
  let alpha := restrictSequence K a
  let physical : (Σ z : ℕ, Σ mp : ℕ, ℕ) → Prop := fun i =>
    parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i
  have hFib (m : ℕ) :
      B.filter (fun i => i∈
        (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
          d L E V Z band slot δ Y m K k alpha).image
          (parityOriginalHistoricalUngatedSourceToSigma434 m)) =
      B.filter (fun i => i.2.2=m ∧ physical i) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi,hImage⟩
      exact ⟨hi,(parity_original_actual_full_odd_psi_sigma_m_fibre_iff434
        d L E V Z band slot δ Y K k alpha m i).mp hImage⟩
    · rintro ⟨hi,hImage⟩
      exact ⟨hi,(parity_original_actual_full_odd_psi_sigma_m_fibre_iff434
        d L E V Z band slot δ Y K k alpha m i).mpr hImage⟩
  have hSupport : ∀i∈B, physical i → i.2.2∈K := by
    intro i hi hPhys
    exact parity_original_actual_full_odd_psi_sigma_image_m_in_fine_K434
      d L E V Z band slot δ Y K k a i hPhys
  calc
    _ = ∑m∈K,∑i∈B.filter (fun i => i.2.2=m ∧ physical i),W i := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hFib m]
    _ = ∑i∈B.filter physical,W i :=
      parity_original_actual_full_odd_cofactor_m_fibre_sum_exact434
        B K (fun i => i.2.2) physical W hSupport
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullOddSourceAllMTwisted -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- ACTUAL ORIGINAL B509 full odd-e e<=2E,n<=3V complex signed
Fourier integrand over ALL genuine b629 fine cofactors m∈K,
with the original complete SOURCE Ybox=ceil(6UV), is EXACTLY the
whole original r0=20 B633 full-positive-Sigma SOURCE-IMAGE finite
3D Fourier integrand. The real original alpha/H0/W1/epsilon source
and the source η_eη_n Schwartz pullback stay literal, as do the
2π normalized physical log(m/U,m'/U,z/Z) phases and smooth ψ_Z.

The proof is not a complex-subsum norm bound: it composes the
kernel-proved one-m true-source χ/Fourier image equality with an
EXACT partition over all m∈K, with no #m,#e,#n multiplicity.
Only the image of the actual SOURCE, not the whole unrestricted
Parity4.17 signed correlation, is identified on this step. -/
theorem parity_eventually_original_actual_full_odd_B509_all_m_source_twisted_eq_sigma_image434
    (S beta gamma : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      ∀ (ζ : EuclideanSpace ℝ (Fin 3))
        (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b),
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let Ybox := Nat.ceil (6*U*V)
      let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
        (Finset.Icc 1 ⌊64*Z⌋₊)
      let image : I → Prop := fun i =>
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ Ybox K k alpha i
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      let Wproj : I → ℂ := fun i => psi i*A i*alpha i.2.2*star (alpha i.2.1)*
        (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
          then (1:ℂ) else 0)
      (∑m∈K,
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
              d L E V band slot δ Ybox m K k,
            let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
            (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q)))) =
      parityOriginal3DPhysicalFiniteTwistedSource434
        (Ball.filter image) Wproj t f ζ := by
  filter_upwards [parity_eventually_original_actual_full_odd_B509_source_twisted_eq_sigma_image434
      S beta gamma hS hbeta hgamma] with L hExact
  refine ⟨hExact.1,?_⟩
  intro hLw prime l u hl hlow K k hk d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ
    ζ buf a b hSmooth hBufSupport
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Ybox := Nat.ceil (6*U*V)
  let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let image : I → Prop := fun i =>
    parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Ybox K k alpha i
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  let Wproj : I → ℂ := fun i =>
    psi i*A i*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0)
  let phase : I → ℂ := fun i => parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)
  have hPart := parity_original_actual_full_odd_psi_sigma_complete_m_partition434
    d L E V Z band slot δ Ybox K k
    (b629ActualFineAlpha434 prime L S gamma l u) Ball
    (fun i : I => Wproj i*phase i)
  change (∑m∈K,
      ∑i∈Ball.filter (fun i => i∈
        (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
          d L E V Z band slot δ Ybox m K k alpha).image
            (parityOriginalHistoricalUngatedSourceToSigma434 m)),
        Wproj i*phase i) =
      ∑i∈Ball.filter image,Wproj i*phase i at hPart
  have hPerM (m : ℕ) (hm : m∈K) :
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot δ Ybox m K k,
          let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
          (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
            parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))) =
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑i∈Ball.filter (fun i => i∈
          (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
            d L E V Z band slot δ Ybox m K k alpha).image
              (parityOriginalHistoricalUngatedSourceToSigma434 m)),
          Wproj i*phase i) := by
    have hOne := hExact.2 hLw prime l u hl hlow K k hk d band slot δ ξ
      rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ m ζ
      buf a b hSmooth hBufSupport
    unfold parityOriginal3DPhysicalFiniteTwistedSource434 at hOne
    exact hOne
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
  calc
    (∑m∈K,
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot δ Ybox m K k,
          let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
          (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
            parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q)))) =
      ∑m∈K,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑i∈Ball.filter (fun i => i∈
          (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
            d L E V Z band slot δ Ybox m K k alpha).image
              (parityOriginalHistoricalUngatedSourceToSigma434 m)),
          Wproj i*phase i) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hPerM m hm
    _ = (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑m∈K,∑i∈Ball.filter (fun i => i∈
        (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
          d L E V Z band slot δ Ybox m K k alpha).image
            (parityOriginalHistoricalUngatedSourceToSigma434 m)),
        Wproj i*phase i) := by rw [Finset.mul_sum]
    _ = (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑i∈Ball.filter image,Wproj i*phase i) := by rw [hPart]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualAllMSourceBallEq417 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- UNCONDITIONAL TRUE ORIGINAL full-odd B509 post-Cauchy complete
fine K-cofactor m SUM (not a fixed m or subset) over e<=2E,n<=3V,
at fixed original signed k and smooth positive dyadic Z, with exact
Ybox=ceil(6UV), real native b629 fine alpha, BOTH original H0
prime slots, all W1/parity/epsilon weights, and real η_eη_n 3D
Schwartz Fourier kernel, is bounded by the ORIGINAL unrestricted
signed Parity(4.17) full χ Fourier-ball norm plus TWO explicitly
paid source-positive Schwartz tail errors:

‖∫_{‖ζ‖≤T} Σ_{m∈K} 𝓕f(ζ) Σ_{(e,m',n) in SOURCE_m(k)}
  ψ_Z(z/Z) α_m α̅_m' A_B633(m,m',z) exp(2πi⟪ζ,t⟫) dζ‖
≤ ‖Σχ cχ ∫_{‖ζ‖≤T} 𝓕f(ζ) B633Parity417_χ(ζ) dζ‖
  + 2 L^(2C_W1) ceil(65Z)(1+log ceil(65Z))^15 M_H(f)/T^H.

This exact B509 SOURCE-to-Sigma transfer uses the full finite
original m sum and fixed-m injective e/n reindex. It is NOT a
false signed-subset inequality, never applies character
orthogonality separately to fractional e, and never restricts
source e to P-free values. To obtain TypeII(4.2), the further
unrestricted signed saving and genuine outer k,Z,branch,Fourier
budgets must still be proved in their exact parameter order. -/
theorem parity_eventually_original_actual_full_odd_all_m_B509_source_ball_le_eq417_two_ghost434
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
      |((2*k:ℤ):ℝ)|≤Z/128 →
      ∀ (buf : ℝ → ℂ) (a b : ℝ)
        (hSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
        (H : ℕ) (T : ℝ), 0<T →
      let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
        i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
      let Ybox := Nat.ceil (6*U*V)
      let N := Finset.Icc 1 ⌊64*Z⌋₊
      let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hBufSupport
      let Mass := L^(2*parityOriginalW1PolylogExponent434)*
        ((Nat.ceil (65*Z):ℕ):ℝ)*
        (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15
      ‖∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        (∑m∈K,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
              d L E V band slot δ Ybox m K k,
            let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
            (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))))‖ ≤
      ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
              (2*k.natAbs) chi 0 0
             parityOriginalHistoricalActualB633FullFourierCofactor434
              L rho xi1 xi2 xi3 U Z k N alpha F.residual
              (2*k.natAbs) chi F.lo F.hi signed
              parityOriginalHistoricalDyadicSmoothPsi434 ζ))‖ +
      2*(Mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  filter_upwards [parity_eventually_original_actual_full_odd_B509_all_m_source_twisted_eq_sigma_image434
      S beta gamma hS hbeta hgamma,
    parity_eventually_original_actual_B633_full_odd_source_image_psi_ball_le_eq417_plus_two_ghost434
      S beta gamma Ck hS hbeta hgamma] with L hTwisted hBound
  refine ⟨hBound.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad hkZ
    buf a b hSmooth hBufSupport H T hT
  dsimp only
  classical
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F0 := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let psi : I → ℂ := fun i => parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z)
  let Ybox := Nat.ceil (6*U*V)
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let Ball := parityOriginalHistoricalActualB633PositiveSigma434 L k N
  let image : I → Prop := fun i => parityOriginalHistoricalFullOddPsiImageAtSigma434
    d L E V Z band slot δ Ybox K k alpha i
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hBufSupport
  let Wproj : I → ℂ := fun i =>
    psi i*A i*alpha i.2.2*star (alpha i.2.1)*
      (if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
        then (1:ℂ) else 0)
  let Mass := L^(2*parityOriginalW1PolylogExponent434)*
    ((Nat.ceil (65*Z):ℕ):ℝ)*
    (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15
  let G : ℂ := ∑chi : DirichletCharacter ℂ (2*k.natAbs),
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0
         parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha F.residual
          (2*k.natAbs) chi F.lo F.hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ))
  let Iphys : ℂ := ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 (Ball.filter image)
      Wproj t f ζ
  have hTwistedAll (ζ : EuclideanSpace ℝ (Fin 3)) :
      (∑m∈K,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot δ Ybox m K k,
          let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
          (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
            parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q)))) =
      parityOriginal3DPhysicalFiniteTwistedSource434
        (Ball.filter image) Wproj t f ζ := by
    exact hTwisted.2 hLw prime l u hl hlow K k hk d band slot δ ξ
      rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ
      ζ buf a b hSmooth hBufSupport
  have hInt :
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        (∑m∈K,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          (∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
              d L E V band slot δ Ybox m K k,
            let fmap := parityOriginalHistoricalUngatedSourceToSigma434 m
            (psi (fmap q)*alpha m*star (alpha q.2.1)*A (fmap q))*
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (fmap q))))) = Iphys := by
    unfold Iphys
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact hTwistedAll ζ
  have hN : ∀z∈N,0<z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have hBoundEq := hBound.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ rho xi1 xi2 xi3 U E V Z signed
    hU hE hV hZ hDyad N hN hkZ buf a b hSmooth hBufSupport H T hT
  change ‖Iphys‖ ≤ ‖G‖+2*(Mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H))
    at hBoundEq
  rw [hInt]
  exact hBoundEq
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqNativeFineCoreNoDoubleRestrict -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- EXACT original B509/native Parity(4.16) prime core: passing the
already K-restricted fine b629 α into `sourceNativePrimeCore`, as
happens in the literal full odd-e B509 SOURCE Fourier-ball, gives
EXACTLY the same whole PrimeSlotCore as passing raw b629 α with
the same K, as required by the existing unconditional Parity(4.17)
χ-Fourier saving theorem. Every component agrees:
alpha, skipped-Q residual c_r, native moving Q `lo`/`hi`, χ,
σ₀,σ₁. No new positive coefficient, residual hypothesis, or
source independence is assumed: K restriction is idempotent.
This closes the otherwise genuine raw-vs-double-restricted α
mismatch between native source and Parity(4.17) kernel interfaces. -/
theorem parity_original_native_source_B509_core_double_fine_restrict_eq_raw434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    sourceNativePrimeCore r d L b slot δ ξ K
      (restrictSequence K alpha) q chi σ₀ σ₁ =
    sourceNativePrimeCore r d L b slot δ ξ K
      alpha q chi σ₀ σ₁ := by
  unfold sourceNativePrimeCore
  congr 1
  funext n
  by_cases hn : n∈K
  · simp [restrictSequence,hn]
  · simp [restrictSequence,hn]

/-- The SOURCE cofactor alpha argument is exactly the raw-core
alpha field of the unconditional original Parity(4.17) saving; no
fine coefficient is replaced and no universal α hypothesis
is used. -/
theorem parity_original_native_B509_double_restrict_fine_alpha_eq_raw_core434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q) :
    restrictSequence K alpha =
      (sourceNativePrimeCore r d L b slot δ ξ K alpha q chi 0 0).alpha := by
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSourceCoreEq417Saving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3100000

/-- DIRECT, UNCONDITIONAL, SOURCE-EXACT original Parity(4.17)
pointwise FULL-CHARACTER Fourier saving for the **same literal
core** that occurs in the full-odd B509 source-image Fourier
ball. The source passes α=restrictSequence(Icc a b)(b629 fine)
INTO `sourceNativePrimeCore`, whereas the previously accepted
Parity(4.17) theorem passes raw b629 α and restricts internally.
The two cores, including full skipped Q residual c_r, native
reserved interval, χ and sigma, are PROVEN DEFINITIONALLY
IDENTICAL by `parity_original_native_source_B509_core_double_fine_restrict_eq_raw434`.
Thus no generic E4.1 assumption, arbitrary-alpha saving, loss
of P-divisibility information or character-count factor occurs.

For arbitrary target D>0 and polynomially shifted ζ frequencies,
choose J,B,S before L then obtain the true ORIGINAL r0=20,
h=-2, a=1,b=2, χ mod 2|k| FULL signed Eq4.17 saving
`‖original source χ cofactor sum‖ ≤ Z L^-D` at each ζ.
This is still pointwise, not yet the bounded Fourier integral
or whole k/Z/fine/source-family TypeII(4.2). -/
theorem parity_eventually_original_actual_B509_source_core_full_chi_fourier_saving434
    (jQ : ℕ) (target Cfreq CZ Ck beta gamma : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original := ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            parityOriginalHistoricalActualB633FullFourierCofactor434
              L rho xi1 xi2 xi3 U Z k N alpha
              (sourceF chi).residual (2*k.natAbs) chi
              (sourceF chi).lo (sourceF chi).hi signed
              parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B633_full_chi_fourier_saving434
      jQ target Cfreq CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSave] with L hSaveL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let K := Finset.Icc a b
  let raw := b629ActualFineAlpha434 prime L S gamma lFine uFine
  let alpha := restrictSequence K raw
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K alpha (2*k.natAbs) chi 0 0
  let rawF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K raw (2*k.natAbs) chi 0 0
  have hCore (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      sourceF chi=rawF chi :=
    parity_original_native_source_B509_core_double_fine_restrict_eq_raw434
      20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq K raw
      (2*k.natAbs) chi 0 0
  have hAlpha (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      (rawF chi).alpha=alpha := rfl
  have hSourceRaw :
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          parityOriginalHistoricalActualB633FullFourierCofactor434
            L rho xi1 xi2 xi3 U Z k N alpha
            (sourceF chi).residual (2*k.natAbs) chi
            (sourceF chi).lo (sourceF chi).hi signed
            parityOriginalHistoricalDyadicSmoothPsi434 ζ) =
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          parityOriginalHistoricalActualB633FullFourierCofactor434
            L rho xi1 xi2 xi3 U Z k N (rawF chi).alpha
            (rawF chi).residual (2*k.natAbs) chi
            (rawF chi).lo (rawF chi).hi signed
            parityOriginalHistoricalDyadicSmoothPsi434 ζ) := by
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [hCore chi, hAlpha chi]
  have hRawSave := hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  change ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha
          (sourceF chi).residual (2*k.natAbs) chi
          (sourceF chi).lo (sourceF chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ‖ ≤ Z*L^(-target)
  rw [hSourceRaw]
  exact hRawSave
end Green64Analytic.Parity

end

end

/-! ## ActualDyadicZCardBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- The number of distinct binary dyadic heights attained by an actual
finite source z-carrier is logarithmic in its *upper* physical z bound,
not proportional to the number of original z or (e,n,m,m') tuples.
The dyadic map is the literal historical 2^(Nat.log 2 z). -/
theorem parity_original_actual_dyadic_z_image_card_le_log434
    (S : Finset ℕ) (Y : ℕ) (hY : ∀ z∈S, z≤Y) :
    (S.image parityOriginalHistoricalActualZDyadicScale434).card ≤
      Nat.log 2 Y + 1 := by
  classical
  let T : Finset ℕ := (Finset.range (Nat.log 2 Y + 1)).image (fun j : ℕ => 2^j)
  have hsub : S.image parityOriginalHistoricalActualZDyadicScale434 ⊆ T := by
    intro Z hZ
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hZ
    have hlog : Nat.log 2 z ≤ Nat.log 2 Y := Nat.log_mono_right (hY z hz)
    apply Finset.mem_image.mpr
    refine ⟨Nat.log 2 z, ?_, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlog)
  calc
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 Y + 1)).card := Finset.card_image_le
    _ = Nat.log 2 Y + 1 := Finset.card_range _

/-- The original source dyadic heights have total positive mass at most
(log_2(Y)+1)Y. This counts each distinct dyad exactly once, without
counting the often much larger underlying physical z-fibres. -/
theorem parity_original_actual_dyadic_z_image_mass_le_log434
    (S : Finset ℕ) (Y : ℕ)
    (hY : ∀ z∈S, z≤Y) (hPos : ∀ z∈S, 0<z) :
    (∑ Z∈S.image parityOriginalHistoricalActualZDyadicScale434, (Z:ℝ)) ≤
      (Nat.log 2 Y + 1 : ℕ) * (Y:ℝ) := by
  classical
  let V := S.image parityOriginalHistoricalActualZDyadicScale434
  have hZ : ∀ Z∈V, (Z:ℝ)≤(Y:ℝ) := by
    intro Z hmem
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hmem
    have hBound : parityOriginalHistoricalActualZDyadicScale434 z≤z :=
      (parity_original_historical_actual_z_in_own_dyad434 z (hPos z hz)).2.1
    exact_mod_cast hBound.trans (hY z hz)
  have hcard : V.card≤Nat.log 2 Y+1 :=
    parity_original_actual_dyadic_z_image_card_le_log434 S Y hY
  have hsum : (∑ Z∈V,(Z:ℝ))≤(V.card:ℝ)*(Y:ℝ) := by
    calc
      _ ≤ ∑ Z∈V,(Y:ℝ) := Finset.sum_le_sum (by intro Z hZmem; exact hZ Z hZmem)
      _ = (V.card:ℝ)*(Y:ℝ) := by simp
  have hYnonneg : (0:ℝ)≤Y := Nat.cast_nonneg _
  have hcast : (V.card:ℝ) ≤ ((Nat.log 2 Y+1:ℕ):ℝ) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcast hYnonneg
  exact hsum.trans hmul
end Green64Analytic.Parity

end

end

/-! ## ActualSignedKDyadicAggregate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- True signed Parity k has at most 2N+1 values once the original
post-Cauchy dyadic e window proves |k|<=N. Both signs are counted;
this is not a per-character or per-cofactor cardinal loss. -/
theorem parity_original_actual_signed_k_set_card_le434
    (KS : Finset ℤ) (N : ℕ) (hKS : ∀ k∈KS, k.natAbs≤N) :
    KS.card≤2*N+1 := by
  classical
  let T : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  have hsub : KS⊆T := by
    intro k hk
    change k∈Finset.Icc (-(N:ℤ)) (N:ℤ)
    rw [Finset.mem_Icc]
    have habs := hKS k hk
    omega
  have hc : T.card=2*N+1 := by
    dsimp [T]
    rw [Int.card_Icc]
    have heq : (N:ℤ)+1-(-(N:ℤ))=((2*N+1:ℕ):ℤ) := by omega
    rw [heq,Int.toNat_natCast]
  exact (Finset.card_le_card hsub).trans_eq hc

/-- Entire original signed k outer and DISTINCT actual source dyadic Z
outer. Every individual complex ball may be genuinely signed and
arbitrary, so we use complex triangle *only after* the full character
projector. We do not replace or truncate any constituent B' amplitude.
The result is exact up to the harmless counted k/Z envelopes. -/
theorem parity_original_actual_signed_k_dyadic_z_global_norm_bound434
    (L D C : ℝ) (hL : 0<L) (hC : 0≤C)
    (KS : Finset ℤ) (N : ℕ) (hKS : ∀ k∈KS, k.natAbs≤N)
    (ZS : Finset ℕ) (Y : ℕ)
    (hZS : ∀ z∈ZS, z≤Y) (hZpos : ∀ z∈ZS, 0<z)
    (F : ℤ → ℕ → ℂ)
    (hCell : ∀ k∈KS, ∀ Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434,
      ‖F k Z‖≤C*(Z:ℝ)*L^(-D)) :
    ‖∑k∈KS, ∑Z∈ZS.image parityOriginalHistoricalActualZDyadicScale434, F k Z‖ ≤
      (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*C*(Y:ℝ)*L^(-D) := by
  classical
  let DY : Finset ℕ := ZS.image parityOriginalHistoricalActualZDyadicScale434
  have hkcard : KS.card≤2*N+1 :=
    parity_original_actual_signed_k_set_card_le434 KS N hKS
  have hzcard : DY.card≤Nat.log 2 Y+1 :=
    parity_original_actual_dyadic_z_image_card_le_log434 ZS Y hZS
  have hzle : ∀Z∈DY,(Z:ℝ)≤(Y:ℝ) := by
    intro Z hZ
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hZ
    have h := (parity_original_historical_actual_z_in_own_dyad434 z (hZpos z hz)).2.1
    exact_mod_cast h.trans (hZS z hz)
  have hPow : 0≤L^(-D) := (Real.rpow_pos_of_pos hL _).le
  let M : ℝ := C*(Y:ℝ)*L^(-D)
  have hM : 0≤M := by dsimp [M]; positivity
  have hBound : ∀ k∈KS, ∀ Z∈DY, ‖F k Z‖≤M := by
    intro k hk Z hz
    calc
      ‖F k Z‖ ≤ C*(Z:ℝ)*L^(-D) := hCell k hk Z hz
      _ ≤ C*(Y:ℝ)*L^(-D) := by
        apply mul_le_mul_of_nonneg_right _ hPow
        exact mul_le_mul_of_nonneg_left (hzle Z hz) hC
  have hTri :
      ‖∑ k∈KS, ∑ Z∈DY, F k Z‖ ≤
        ∑ k∈KS, ∑ Z∈DY, ‖F k Z‖ := by
    calc
      _ ≤ ∑ k∈KS, ‖∑ Z∈DY, F k Z‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ k∈KS, ∑ Z∈DY, ‖F k Z‖ := by
        apply Finset.sum_le_sum
        intro k hk
        exact norm_sum_le _ _
  have hFinite : (∑ k∈KS, ∑ Z∈DY, ‖F k Z‖) ≤
      ((KS.card:ℝ)*(DY.card:ℝ))*M := by
    calc
      _ ≤ ∑ k∈KS, ∑ Z∈DY, M := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro Z hz
        exact hBound k hk Z hz
      _ = ((KS.card:ℝ)*(DY.card:ℝ))*M := by simp [mul_assoc]
  have hkc : (KS.card:ℝ)≤((2*N+1:ℕ):ℝ) := by exact_mod_cast hkcard
  have hzc : (DY.card:ℝ)≤((Nat.log 2 Y+1:ℕ):ℝ) := by exact_mod_cast hzcard
  have hProd : (KS.card:ℝ)*(DY.card:ℝ) ≤
      ((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ) := by
    exact mul_le_mul hkc hzc (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ((KS.card:ℝ)*(DY.card:ℝ))*M := hTri.trans hFinite
    _ ≤ (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*M :=
      mul_le_mul_of_nonneg_right hProd hM
    _ = (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*C*(Y:ℝ)*L^(-D) := by
      dsimp [M]; ring
end Green64Analytic.Parity

end

end

/-! ## ActualKZLossAbsorption -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- The exact signed-k and distinct source-dyadic-Z counting loss is
absorbed by a fixed extra inverse-log precision. N bounds the original
signed Parity (4.13) k range; Y is a containing cap for ORIGINAL z, not
an extra post-Cauchy u gate. Original geometry supplies Y << exp L
L^(K0+88) and logY<=2L. No #e,#n,#m or #characters is charged.
This is the numerical aggregation for ONE original fine family. -/
theorem parity_original_actual_kZ_counted_loss_absorbed434
    (L Agoal D C Ck K0 Cbox : ℝ) (N Y : ℕ)
    (hL : 1≤L) (hC : 0≤C) (hCk : 0≤Ck)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hN : N≤Nat.ceil (L^Ck))
    (hY : (Y:ℝ)≤25*Cbox*Real.exp L*L^(K0+88))
    (hYpos : 1≤Y) (hLogY : Real.log (Y:ℝ)≤2*L)
    (hD : Agoal+Ck+K0+90≤D) :
    (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*C*(Y:ℝ)*L^(-D) ≤
      (125*Cbox*(1+2/Real.log 2)*C)*Real.exp L*L^(-Agoal) := by
  have hLp : 0<L := by linarith
  have hpowCk : 1≤L^Ck := Real.one_le_rpow hL hCk
  have hpK : 0≤L^Ck := (Real.rpow_pos_of_pos hLp _).le
  have hNceil : (N:ℝ)≤L^Ck+1 := by
    have hnc : (N:ℝ)≤((Nat.ceil (L^Ck)):ℝ) := by exact_mod_cast hN
    exact hnc.trans (Nat.ceil_lt_add_one hpK).le
  have hKcount : ((2*N+1:ℕ):ℝ)≤5*L^Ck := by
    push_cast
    linarith
  have hLogTwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hNatLog : ((Nat.log 2 Y:ℕ):ℝ)≤2*L/Real.log 2 := by
    have h := Real.natLog_le_logb Y 2
    apply h.trans
    unfold Real.logb
    exact div_le_div_of_nonneg_right hLogY hLogTwo.le
  let Cdyad : ℝ := 1+2/Real.log 2
  have hCdyad : 0≤Cdyad := by dsimp [Cdyad]; positivity
  have hZcount : ((Nat.log 2 Y+1:ℕ):ℝ)≤Cdyad*L := by
    calc
      _ = ((Nat.log 2 Y:ℕ):ℝ)+1 := by push_cast; ring
      _ ≤ 2*L/Real.log 2+1 := by linarith
      _ ≤ 2*L/Real.log 2+L := by linarith
      _ = Cdyad*L := by dsimp [Cdyad]; ring
  have hYnonneg : (0:ℝ)≤Y := Nat.cast_nonneg _
  have hYCap : 0≤25*Cbox*Real.exp L*L^(K0+88) := by positivity
  have hCount :
      ((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ)*(Y:ℝ) ≤
        (5*L^Ck)*(Cdyad*L)*(25*Cbox*Real.exp L*L^(K0+88)) := by
    have hprod : ((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ) ≤
        (5*L^Ck)*(Cdyad*L) := by
      exact mul_le_mul hKcount hZcount (Nat.cast_nonneg _) (by positivity)
    exact mul_le_mul hprod hY hYnonneg (by positivity)
  have hCoef : 0≤C*L^(-D) := by positivity
  have hPower : L^Ck*L*L^(K0+88)*L^(-D) = L^(Ck+K0+89-D) := by
    calc
      _ = (L^Ck*L^(1:ℝ))*(L^(K0+88)*L^(-D)) := by simp only [Real.rpow_one]; ring
      _ = L^(Ck+1)*L^(K0+88+(-D)) := by rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
      _ = L^(Ck+1+(K0+88+(-D))) := by rw [←Real.rpow_add hLp]
      _ = L^(Ck+K0+89-D) := by congr 1; ring
  have hExp : Ck+K0+89-D ≤ -Agoal := by linarith
  have hPowerLe : L^(Ck+K0+89-D)≤L^(-Agoal) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  have hCoefPos : 0≤(125*Cbox*Cdyad*C)*Real.exp L := by positivity
  calc
    _ = (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ)*(Y:ℝ))*(C*L^(-D)) := by ring
    _ ≤ ((5*L^Ck)*(Cdyad*L)*(25*Cbox*Real.exp L*L^(K0+88)))*(C*L^(-D)) :=
      mul_le_mul_of_nonneg_right hCount hCoef
    _ = ((125*Cbox*Cdyad*C)*Real.exp L)*(L^Ck*L*L^(K0+88)*L^(-D)) := by ring
    _ = ((125*Cbox*Cdyad*C)*Real.exp L)*L^(Ck+K0+89-D) := by rw [hPower]
    _ ≤ ((125*Cbox*Cdyad*C)*Real.exp L)*L^(-Agoal) :=
      mul_le_mul_of_nonneg_left hPowerLe hCoefPos
    _ = (125*Cbox*(1+2/Real.log 2)*C)*Real.exp L*L^(-Agoal) := by
      dsimp [Cdyad]
end Green64Analytic.Parity

end

end

/-! ## BPrimeAllMTrueSigmaReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- A genuine Sigma point in the fixed-m original full-odd source
image remembers its external Cauchy cofactor m exactly. In particular,
there is no additional multiplicity when summing the fixed-m signed
reindex over all original fine-cofactor m. -/
theorem parity_original_ungated_sigma_source_image_remembers_m434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hi : i ∈ (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
      d L E V Z band slot δ Y m K k alpha).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m)) :
    i.2.2 = m := by
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hi
  rfl

/-- The exact outer sum over ALL original cofactor m has no extra
copy-count: the FULL-ODD original post-Cauchy (e,n,m,m',z) signed
coefficient equals the full Parity Sigma source-image signed coefficient.
The arbitrary W permits the literal H0, W1, epsilon, source Schwartz
Fourier phase and full-character-projected mask; no Pfree-e gate,
subsum-norm monotonicity, or quotient by a putative multiplicity is used.
Only roughness of the actual alpha when nonzero is needed. -/
theorem parity_original_ungated_full_odd_Bprime_all_m_to_true_sigma434
    (d : ℕ) (L E V Z : ℝ) (hL : 1≤L) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ)
    (hRough : ∀t,alpha t≠0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) t)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
      (Finset.Icc 1 ⌊64*Z⌋₊)
    let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let f := parityOriginalHistoricalUngatedSourceToSigma434
    (∑ m∈K, ∑q∈S m,
       parityOriginalHistoricalDyadicSmoothPsi434
         ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
         alpha m * star (alpha q.2.1) * W (f m q)) =
    ∑i∈B.filter (fun i => i.2.2∈K ∧
       parityOriginalHistoricalFullOddPsiImageAtSigma434
         d L E V Z band slot δ Y K k alpha i),
       parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
         alpha i.2.2 * star (alpha i.2.1) * W i := by
  classical
  dsimp only
  let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let f := parityOriginalHistoricalUngatedSourceToSigma434
  let img := fun m => (parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y m K k alpha).image (f m)
  let g : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      alpha i.2.2 * star (alpha i.2.1) * W i
  have hRemember (i : Σ z : ℕ, Σ mp : ℕ, ℕ) (m : ℕ)
      (hi : i∈img m) : i.2.2 = m :=
    parity_original_ungated_sigma_source_image_remembers_m434
      d L E V Z band slot δ Y m K k alpha i hi
  have hFixed (m : ℕ) :
    (∑q∈S m,
       parityOriginalHistoricalDyadicSmoothPsi434
         ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
         alpha m * star (alpha q.2.1) * W (f m q)) =
    ∑i∈B.filter (fun i => i∈img m),g i := by
    have hBase := parity_original_ungated_actual_full_odd_psi_source_eq_real_417_sigma_image434
      d L E V Z hL hZ band slot δ Y m K k hk alpha hRough W
    change (∑q∈S m,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
        alpha m * star (alpha q.2.1) * W (f m q)) =
      ∑i∈B.filter (fun i => i∈img m),
        parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        alpha m * star (alpha i.2.1) * W i at hBase
    rw [hBase]
    apply Finset.sum_congr rfl
    intro i hi
    have hh := hRemember i m (Finset.mem_filter.mp hi).2
    simp only [g,hh]
  have hIndex (i : Σ z : ℕ, Σ mp : ℕ, ℕ) (m : ℕ) :
      i∈img m ↔ m=i.2.2 ∧
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ Y K k alpha i := by
    constructor
    · intro hi
      have hh := hRemember i m hi
      constructor
      · exact hh.symm
      · simpa [parityOriginalHistoricalFullOddPsiImageAtSigma434, img, hh] using hi
    · rintro ⟨rfl,hi⟩
      exact hi
  calc
    (∑m∈K, ∑q∈S m,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
        alpha m * star (alpha q.2.1) * W (f m q)) =
      ∑m∈K, ∑i∈B.filter (fun i => i∈img m), g i := by
        apply Finset.sum_congr rfl
        intro m _
        exact hFixed m
    _ = ∑i∈B, ∑m∈K,
        if i∈img m then g i else 0 := by
          simp only [Finset.sum_filter]
          rw [Finset.sum_comm]
    _ = ∑i∈B,
        if i.2.2∈K ∧ parityOriginalHistoricalFullOddPsiImageAtSigma434
            d L E V Z band slot δ Y K k alpha i then g i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [hIndex]
          by_cases him : parityOriginalHistoricalFullOddPsiImageAtSigma434
            d L E V Z band slot δ Y K k alpha i
          · simp [him]
          · simp [him]
    _ = ∑i∈B.filter (fun i => i.2.2∈K ∧
          parityOriginalHistoricalFullOddPsiImageAtSigma434
            d L E V Z band slot δ Y K k alpha i), g i := by
          simp only [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## BPrimeAllMTrueSigmaFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Exact ORIGINAL whole-m source-image Fourier BALL equality at fixed
signed k,Z. Its LHS enumerates physical odd e, m, m' and n exactly
once; its RHS enumerates the literal positive B633 Sigma image. The
same real nonlinear Parity(4.14) Schwartz kernel and true log triples
are present on both sides. Any W can be the exact original H0/W1,
signed epsilon, prime-rest and fully projected character coefficient;
this is an equality, not a false inequality between complex subsums. -/
theorem parity_original_full_odd_Bprime_all_m_source_fourier_ball_eq_sigma434
    (d : ℕ) (L E V U Z : ℝ) (hLw : 8≤L)
    (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ)
    (hRough : ∀t,alpha t≠0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) t)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ, buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) :
    let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
    let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
      (Finset.Icc 1 ⌊64*Z⌋₊)
    let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let phi := parityOriginalHistoricalUngatedSourceToSigma434
    let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
      parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hLw U E V Z k buf a b hSmooth hSupport
    let Wproj : I → ℂ := fun i =>
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        alpha i.2.2 * star (alpha i.2.1) * W i
    (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑m∈K, ∑q∈S m,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
              alpha m * star (alpha q.2.1) * W (phi m q) *
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m q)))) =
    ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (B.filter (fun i => i.2.2∈K ∧
          parityOriginalHistoricalFullOddPsiImageAtSigma434
            d L E V Z band slot δ Y K k alpha i)) Wproj t f ζ := by
  classical
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot δ Y m K k
  let phi := parityOriginalHistoricalUngatedSourceToSigma434
  let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hSupport
  let Wproj : I → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      alpha i.2.2 * star (alpha i.2.1) * W i
  apply integral_congr_ae
  filter_upwards [] with ζ
  have hR := parity_original_ungated_full_odd_Bprime_all_m_to_true_sigma434
    d L E V Z (by linarith : 1≤L) hZ band slot δ Y K k hk alpha hRough
    (fun i => W i * parityOriginal3DPhysicalLogFourierPhase434 ζ (t i))
  change
    (∑m∈K, ∑q∈S m,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
        alpha m * star (alpha q.2.1) *
        (W (phi m q) * parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m q)))) =
    ∑i∈B.filter (fun i => i.2.2∈K ∧
      parityOriginalHistoricalFullOddPsiImageAtSigma434
        d L E V Z band slot δ Y K k alpha i),
        parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        alpha i.2.2 * star (alpha i.2.1) *
        (W i * parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)) at hR
  dsimp only [parityOriginal3DPhysicalFiniteTwistedSource434]
  congr 1
  calc
    (∑m∈K, ∑q∈S m,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
        alpha m * star (alpha q.2.1) * W (phi m q) *
        parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m q))) =
      ∑m∈K, ∑q∈S m,
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
          alpha m * star (alpha q.2.1) *
          (W (phi m q) * parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m q))) := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro q _
            ring
    _ = ∑i∈B.filter (fun i => i.2.2∈K ∧
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ Y K k alpha i),
        parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        alpha i.2.2 * star (alpha i.2.1) *
        (W i * parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)) := hR
    _ = ∑i∈B.filter (fun i => i.2.2∈K ∧
        parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ Y K k alpha i),
        Wproj i * parityOriginal3DPhysicalLogFourierPhase434 ζ (t i) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [Wproj]
          ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeFullCharacterSourceBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- The true source Sigma-image forces its retained fine m coefficient
nonzero; since the original fine alpha is supported on K, the all-m
image cannot contain a spurious external m outside K. -/
theorem parity_original_full_odd_psi_sigma_image_m_in_fine_support434
    (d : ℕ) (L E V Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (alpha : ℕ → ℂ)
    (hAlpha : ∀n,alpha n≠0 → n∈K)
    (i : Σ z : ℕ, Σ mp : ℕ, ℕ)
    (hi : parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i) : i.2.2∈K := by
  change i∈(parityOriginalHistoricalUngatedActualPsiNonzeroSigmaSource434
    d L E V Z band slot δ Y i.2.2 K k alpha).image
    (parityOriginalHistoricalUngatedSourceToSigma434 i.2.2) at hi
  obtain ⟨q,hq,_⟩ := Finset.mem_image.mp hi
  exact hAlpha i.2.2 (Finset.mem_filter.mp hq).2.1

/-- Exact genuine source B' to full source-image B633 Fourier ball,
with the WHOLE odd-integral Parity (2.6) projector factor in the source
summand BEFORE restricting Sigma or taking norms. Every original
post-Cauchy physical (e,n,m,m',z) term is counted once. This theorem
retains the genuine Parity(4.14) Schwartz f, both alpha coefficients,
original dyadic psi, signed k and 2|k|-character modulus encoded
in the full projector. No individual-character cancellation or false
complex-subsum inequality is used. -/
theorem parity_original_full_odd_Bprime_all_m_projected_fourier_ball_eq_source_image434
    (d : ℕ) (L E V U Z : ℝ) (hLw : 8≤L)
    (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (alpha : ℕ → ℂ)
    (hRough : ∀t,alpha t≠0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) t)
    (hAlpha : ∀n,alpha n≠0 → n∈K)
    (A : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) :
    let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
    let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
      (Finset.Icc 1 ⌊64*Z⌋₊)
    let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let phi := parityOriginalHistoricalUngatedSourceToSigma434
    let t : I → EuclideanSpace ℝ (Fin 3) := fun i =>
      parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hLw U E V Z k buf a b hSmooth hSupport
    let mask : I → ℂ := fun i =>
      if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
      then 1 else 0
    let Wproj : I → ℂ := fun i =>
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
        A i * alpha i.2.2 * star (alpha i.2.1) * mask i
    (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑m∈K, ∑q∈S m,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 q.1 m q.2.1 q.2.2:ℝ)/Z) *
              alpha m * star (alpha q.2.1) *
              (A (phi m q) * mask (phi m q)) *
              parityOriginal3DPhysicalLogFourierPhase434 ζ (t (phi m q)))) =
    ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (B.filter (fun i => parityOriginalHistoricalFullOddPsiImageAtSigma434
          d L E V Z band slot δ Y K k alpha i)) Wproj t f ζ := by
  classical
  dsimp only
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let B := parityOriginalHistoricalActualB633PositiveSigma434 L k
    (Finset.Icc 1 ⌊64*Z⌋₊)
  let mask : I → ℂ := fun i =>
    if k∣(i.2.1:ℤ)-(i.2.2:ℤ) ∧ Odd (((i.2.1:ℤ)-(i.2.2:ℤ))/k)
    then 1 else 0
  let Wproj : I → ℂ := fun i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      A i * alpha i.2.2 * star (alpha i.2.1) * mask i
  have hFilt : B.filter (fun i => i.2.2∈K ∧
      parityOriginalHistoricalFullOddPsiImageAtSigma434
        d L E V Z band slot δ Y K k alpha i) =
    B.filter (fun i => parityOriginalHistoricalFullOddPsiImageAtSigma434
      d L E V Z band slot δ Y K k alpha i) := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.2⟩
    · intro hi
      obtain ⟨hbi,him⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨hbi,parity_original_full_odd_psi_sigma_image_m_in_fine_support434
          d L E V Z band slot δ Y K k alpha hAlpha i him,him⟩
  have hFourier := parity_original_full_odd_Bprime_all_m_source_fourier_ball_eq_sigma434
    d L E V U Z hLw hU hE hV hZ band slot δ Y K k hk
    alpha hRough (fun i => A i * mask i) buf a b hSmooth hSupport T
  dsimp only at hFourier
  rw [hFilt] at hFourier
  convert hFourier using 1
  apply integral_congr_ae
  filter_upwards [] with ζ
  dsimp only [parityOriginal3DPhysicalFiniteTwistedSource434]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeAllMPhysicalCharacterMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- At every TRUE original all-odd post-Cauchy e,m,m',n atom,
without a Pfree-e gate, the WHOLE Parity (2.6) character projector
with modulus 2|k| is exactly 1. The oddness is proved from the
source FULL-odd e support and correct determinant m'-m=e*k;
it is not claimed for each individual Dirichlet character. -/
theorem parity_original_all_m_full_odd_Bprime_source_character_mask_one434
    (d : ℕ) (L E V : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ)
    (q : ℕ × (ℕ × ℕ))
    (hq : q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k) :
    (if k∣((parityOriginalHistoricalUngatedSourceToSigma434 m q).2.1:ℤ)-
        ((parityOriginalHistoricalUngatedSourceToSigma434 m q).2.2:ℤ) ∧
      Odd (((((parityOriginalHistoricalUngatedSourceToSigma434 m q).2.1:ℤ)-
        ((parityOriginalHistoricalUngatedSourceToSigma434 m q).2.2:ℤ))/k))
    then (1:ℂ) else 0)=1 := by
  obtain ⟨_,_,_,he,hNe,hValid,hK⟩ :=
    parity_original_ungated_actual_fixed_m_k_source_legal434
      d L E V band slot δ Y m K k q hq
  dsimp only [parityOriginalHistoricalUngatedSourceToSigma434]
  exact parity_original_ungated_actual_source_odd_shift_mask_one434
    d L band slot δ Y q.1 m q.2.1 q.2.2 k he hNe hValid hK

/-- Exact insertion of the COMPLETE odd-integral character projector
in the original physical (e,n,m,m') post-Cauchy complex sum before
Fourier transform or restricting source images. Arbitrary G retains
all original alpha, Q/P/H0/W1/epsilon and smooth η/ψ weights. -/
theorem parity_original_all_m_full_odd_Bprime_source_character_mask_insert434
    (d : ℕ) (L E V : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ)
    (G : ℕ → (ℕ × (ℕ × ℕ)) → ℂ) :
    let S := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot δ Y m K k
    let phi := parityOriginalHistoricalUngatedSourceToSigma434
    (∑m∈K,∑q∈S m,G m q) =
    ∑m∈K,∑q∈S m,G m q *
      (if k∣((phi m q).2.1:ℤ)-((phi m q).2.2:ℤ) ∧
           Odd (((((phi m q).2.1:ℤ)-((phi m q).2.2:ℤ))/k))
        then (1:ℂ) else 0) := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro q hq
  rw [parity_original_all_m_full_odd_Bprime_source_character_mask_one434
    d L E V band slot δ Y m K k q hq]
  simp
end Green64Analytic.Parity

end

end

